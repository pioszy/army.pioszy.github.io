/* =====================================================================
 * Army Ability Injector — Tabletop Simulator saved-army helper
 * ---------------------------------------------------------------------
 * 1. Loads an army DEFINITION (Battlescribe-style roster JSON) and walks
 *    the whole tree collecting every ability definition:
 *      - rule entries          : { name, description }
 *      - "Abilities" profiles  : profile.name + characteristic named
 *                                "Description" whose value is in $text
 * 2. Loads a Tabletop Simulator SAVED ARMY file (ObjectStates[].Description)
 *    and finds which abilities appear there:
 *      - exact match first, fuzzy (Levenshtein similarity) as fallback
 * 3. Shows every proposal with a checkbox (checked by default), plus an
 *    "All abilities" panel where each ability can be enabled/disabled on
 *    all units at once and whose description text is editable — the edited
 *    value is what gets injected when Process runs.
 * 4. "Process" rewrites ONLY the Description fields of matched objects —
 *       "*ability name*"            ->  "*ability name\n<description>*"
 *    and downloads the modified save file (CRLF + 2-space indent, like TTS).
 * ===================================================================== */

'use strict';

/* ----------------------------- state ---------------------------------- */
const state = {
  defData: null,          // parsed definition JSON
  savedRawText: '',       // original text of the saved army file
  savedData: null,        // parsed (pristine) saved army JSON — used for matching only
  abilities: [],          // [{ name, desc }] unique ability definitions
  proposals: [],          // see buildProposals()
  descOverrides: {}       // normKey(ability) -> edited description text ('' = intentionally emptied → skipped); key absent = use original
};

const $ = sel => document.querySelector(sel);

/* --------------------------- small utils ------------------------------ */
function escapeRe(s) { return String(s).replace(/[.*+?^${}()|[\]\\]/g, '\\$&'); }

/** lowercase alphanumeric key used for dedupe / fuzzy matching */
function normKey(s) { return String(s || '').toLowerCase().replace(/[^a-z0-9]+/g, ''); }

/* Levenshtein distance (two-row DP — names are short strings) */
function levenshtein(a, b) {
  if (!a.length && !b.length) return 0;
  let prev = new Array(b.length + 1);
  for (let j = 0; j <= b.length; j++) prev[j] = j;
  for (let i = 1; i <= a.length; i++) {
    const cur = [i];
    for (let j = 1; j <= b.length; j++) {
      const cost = a[i - 1] === b[j - 1] ? 0 : 1;
      cur[j] = Math.min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + cost);
    }
    prev = cur;
  }
  return prev[b.length];
}

/** similarity in [0..1], 1 === identical */
function similarityRatio(a, b) {
  const la = a.length, lb = b.length;
  if (!la && !lb) return 1;
  const d = levenshtein(a, b);
  return (Math.max(la, lb) - d) / Math.max(la, lb);
}

function truncate(s, n) { s = String(s || ''); return s.length > n ? s.slice(0, n).trimEnd() + ' …' : s; }

/** Does the user have an explicit override for this ability's description? */
function hasOverride(pOrName) {
  const key = normKey(typeof pOrName === 'string' ? pOrName : (pOrName && pOrName.abilityName));
  return Object.prototype.hasOwnProperty.call(state.descOverrides, key);
}

/** Description text to inject for a proposal: user edit wins over the original; '' means "skip". */
function descriptionFor(p) {
  const ov = state.descOverrides[normKey(p.abilityName)];
  if (ov === undefined) return p.descText; // no explicit override → original definition text
  return String(ov);                       // may be empty string on purpose → caller skips injection
}

/* ===================================================================== *
 * 1. COLLECT ABILITY DEFINITIONS FROM THE ARMY DEFINITION FILE           *
 * ===================================================================== */
function collectAbilities(root) {
  const map = new Map(); // normKey -> { name, desc } (keeps the longest description per ability)

  function add(name, desc) {
    if (!name || !desc) return;
    name = String(name).trim();
    desc = String(desc).replace(/\s+$/g, '').trimStart().trimEnd();
    if (!name || !desc) return;
    const key = normKey(name);
    if (key.length < 3) return; // skip junk like "A", "-", etc.
    const existing = map.get(key);
    if (!existing || desc.length > existing.desc.length) {
      map.set(key, { name: existing ? existing.name : name, desc });
    }
  }

  function walk(node) {
    if (Array.isArray(node)) { for (const x of node) walk(x); return; }
    if (!node || typeof node !== 'object') return;

    // form A — rule entries: { "name": "...", "description": "..." , ...}
    if (typeof node.name === 'string' && typeof node.description === 'string') {
      add(node.name, node.description);
    }

    // form B — profile of type "Abilities" with a characteristic named Description ($text)
    if (Array.isArray(node.characteristics)) {
      const c = node.characteristics.find(
        ch => ch && typeof ch === 'object' && /^description$/i.test(String(ch.name || '')) && typeof ch.$text === 'string'
      );
      if (c && typeof node.name === 'string') add(node.name, c.$text);
    }

    for (const v of Object.values(node)) walk(v); // recurse into every child value
  }

  try { walk(root); } catch (_) { /* defensive — keep what we have */ }
  return Array.from(map.values());
}

/* ===================================================================== *
 * MATCHING: find where an ability name occurs inside a Description       *
 * --------------------------------------------------------------------- *
 * Supported shapes (exact, case-insensitive):                            *
 *   **Ability Name** / *Ability Name*     -> markdown bold markers       *
 *   "Ability Name" alone on its own line  -> how this TTS save lists them*
 * ===================================================================== */

/** Locate the first occurrence of `targetName`; returns {start,end} covering just the name text (asterisks excluded), or null. */
function locateRegionInText(text, targetName) {
  const e = escapeRe(targetName);

  // a) wrapped in asterisks: *name* / **name** — region is only the inner name part
  let re = new RegExp('(\\*{1,2})' + e + '\\1', 'i');
  let m = re.exec(text);
  if (m) {
    const stars = m[1].length;
    return { start: m.index + stars, end: m.index + m[0].length - stars };
  }

  // b) name alone on its own line — the way this TTS save stores ability lists
  re = new RegExp('(^|\\r?\\n)[ \\t]*' + e + '(?:[ \\t]*(?=\\r?\\n|$))', 'i');
  m = re.exec(text);
  if (m) {
    let idx = m.index + m[1].length; // skip the leading newline capture group
    while (idx < text.length && /[ \t]/.test(text[idx])) idx++;
    return { start: idx, end: Math.min(idx + targetName.length, text.length) };
  }

  return null;
}

/** Returns true when `target` occurs in `text` as *name* / **name** or alone on its own line. */
function locateTarget(text, target) {
  return !!locateRegionInText(text, target);
}

/** Insert `desc` right after the first occurrence of `targetName`. Returns new text or null when not found.
 * Output format (decorators are literal strings in the output file):
 *   [aaaaaa]{ability name}[-]\n[666666]<description>[-] */
function injectAfter(text, targetName, desc) {
  const e = escapeRe(targetName);

  // decorators — literal open/close markers around each part of the injected block
  const NAME_DEC_OPEN = '',   NAME_DEC_CLOSE = '';
  const DESC_DEC_OPEN = '[cccccc]',    DESC_DEC_CLOSE = '[-]';

  // a) wrapped in asterisks (single or double): "*name*" -> "[aaaaaa]*name*[-]\n[666666]<desc>[-]"
  let re = new RegExp('(\\*{1,2})' + e + '\\1', 'i');
  const mWrap = re.exec(text);
  if (mWrap) {
    const starLen = mWrap[1].length;
    // keep the original casing/markup exactly as stored in the file between the asterisks
    const inner = mWrap[0].slice(starLen, mWrap[0].length - starLen) || targetName;
    return text.slice(0, mWrap.index)
      + NAME_DEC_OPEN + mWrap[1] + inner + mWrap[1] + NAME_DEC_CLOSE
      + '\n' + DESC_DEC_OPEN + desc + DESC_DEC_CLOSE
      + text.slice(mWrap.index + mWrap[0].length);
  }

  // b) name alone on its own line — wrap the name, then append the description (decorated):
  re = new RegExp('(^|\\r?\\n)[ \\t]*' + e + '(?:[ \\t]*(?=\\r?\\n|$))', 'i');
  const mLine = re.exec(text);
  if (mLine) {
    let idx = mLine.index + mLine[1].length; // skip leading newline capture group
    while (idx < text.length && /[ \t]/.test(text[idx])) idx++;
    const endIdx = Math.min(idx + targetName.length, text.length);
    return text.slice(0, idx)
      + NAME_DEC_OPEN + text.slice(idx, endIdx) + NAME_DEC_CLOSE
      + '\n' + DESC_DEC_OPEN + desc + DESC_DEC_CLOSE
      + text.slice(endIdx);
  }

  return null; // not found — caller must skip this proposal
}

/* ===================================================================== *
 * BUILD PROPOSALS (exact first, then fuzzy fallback per object)          *
 * ===================================================================== */
function getDescText(obj) {
  if (!obj || typeof obj !== 'object') return '';
  const d = ('Description' in obj && typeof obj.Description === 'string') ? obj.Description
          : (('description' in obj && typeof obj.description === 'string') ? obj.description : '');
  return d;
}

function getNickname(obj) {
  if (!obj || typeof obj !== 'object') return '(unknown object)';
  let n = (typeof obj.Nickname === 'string' && obj.Nickname.trim()) ? obj.Nickname
        : ((typeof obj.Name === 'string' && obj.Name.trim()) ? obj.Name + ' (' + (obj.GUID || '?') + ')'
        : String(obj.GUID || '(no name)'));
  n = n.replace(/\[[0-9a-fA-F]{6}\]/g, '').trim(); // strip TTS color codes like [dc61ed] / [-]
  return n || String(obj.GUID || '');
}

function buildProposals(thresholdPct) {
  const proposals = [];
  if (!state.savedData || !Array.isArray(state.savedData.ObjectStates)) return proposals;
  const threshold = Math.min(0.97, Math.max(0.5, (thresholdPct ?? 82) / 100));

  state.abilities.forEach((ability, aIdx) => {
    for (let i = 0; i < state.savedData.ObjectStates.length; i++) {
      const obj = state.savedData.ObjectStates[i];
      if (!obj || typeof obj !== 'object') continue;
      const D = getDescText(obj);
      if (!D) continue;

      // ---- exact match (name as written in the definition file) ----
      let targetName = null, fuzzy = false, score = 1;
      if (locateTarget(D, ability.name)) {
        targetName = ability.name;
      } else {
        // ---- fuzzy fallback: best similar standalone line inside this Description ----
        const lines = D.split(/\r?\n/).map(l => l.trim()).filter(Boolean);
        let bestLine = null, bestScore = 0;
        for (const raw of lines) {
          if (!raw || raw.length < 3 || raw.length > 80) continue; // skip weapon stat rows etc.
          const lineNorm = normKey(raw.replace(/\*+/g, ''));
          let s = similarityRatio(lineNorm, normKey(ability.name));
          if (s >= threshold && s > bestScore) { bestScore = s; bestLine = raw.replace(/^\*+|\*+$/g, '').trim(); }
        }
        if (bestLine !== null && locateTarget(D, bestLine)) { targetName = bestLine; fuzzy = true; score = bestScore; }
      }

      if (!targetName) continue; // no match for this ability on this object

      proposals.push({
        id: 'p' + aIdx + '_' + i,
        objIndex: i,
        nickname: getNickname(obj),
        abilityName: ability.name,
        descText: ability.desc,
        targetText: targetName, // the exact text we will locate & inject after (may differ from ability name if fuzzy)
        fuzzy, score
      });
    }
  });

  return proposals;
}

/* ===================================================================== *
 * PROCESS — apply checked proposals to a fresh copy of the save file     *
 * --------------------------------------------------------------------- *
 * Only Description fields are modified. Everything else in the parsed   *
 * object tree is left untouched, and output keeps TTS formatting        *
 * (2-space indent + CRLF line endings).                                 *
 * ===================================================================== */
function processCheckedProposals(checkedIds) {
  const data = JSON.parse(state.savedRawText); // pristine deep clone from the original text
  if (!Array.isArray(data.ObjectStates)) throw new Error('ObjectStates array not found in saved army file.');

  let appliedCount = 0, failed = [];

  for (const p of state.proposals) {
    if (!checkedIds.has(p.id)) continue; // only checked proposals are applied — unchecked ones must be left alone
    const obj = data.ObjectStates[p.objIndex];
    if (!obj || typeof obj !== 'object') { failed.push(p.abilityName); continue; }

    let descText, keyUsed;
    if ('Description' in obj && typeof obj.Description === 'string') { descText = obj.Description; keyUsed = 'Description'; }
    else if ('description' in obj)  { descText = String(obj.description ?? ''); keyUsed = 'description'; }
    else continue;

    // user-edited description (from the "All abilities" panel) wins over the original definition text
    const descToUse = descriptionFor(p);
    if (!descToUse.trim()) { failed.push(truncate(p.abilityName, 30) + ' (description emptied → skipped)'); continue; }

    const updated = injectAfter(descText, p.targetText, descToUse);
    if (updated === null || updated === descText) { failed.push(p.abilityName + ' → ' + truncate(getNickname(obj), 30)); continue; }

    obj[keyUsed] = updated; // ONLY the description field is modified — nothing else in this object or file
    appliedCount++;
  }

  return { data, appliedCount, failed };
}

/** Serialize like TTS does: 2-space indent + CRLF line endings. */
function serializeLikeTts(data) {
  let out = JSON.stringify(data, null, 2);
  if (out && !/\r\n/.test(out.slice(0, 40))) out = out.replace(/\n/g, '\r\n'); // restore Windows newlines like the original file
  return out;
}

function downloadText(filename, text) {
  const blob = new Blob([text], { type: 'application/json' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = filename || 'saved-army-updated.json';
  document.body.appendChild(a); // required for Firefox
  a.click();
  setTimeout(() => { URL.revokeObjectURL(url); a.remove(); }, 500);
}

/* ===================================================================== *
 * UI WIRING                                                              *
 * ===================================================================== */
function setPill(el, cls, html) { el.className = 'status-pill ' + cls; el.innerHTML = html; }

async function handleDefinitionFile(file) {
  const statusEl = $('#defStatus');
  try {
    state.defData = JSON.parse(await file.text()); // throws on invalid JSON — good, we want to know
    state.abilities = collectAbilities(state.defData);
    if (!state.abilities.length) throw new Error('no ability definitions found in this file');

    setPill(statusEl, 'status-ok', '&#10003; <b>' + escapeHtml(file.name) + '</b> — ' + state.abilities.length + ' unique abilities collected');
    const dz = document.querySelector('.drop-zone[for="defFileInput"]') || file.closest('label');
    if (dz && dz.classList.contains('drop-zone')) dz.classList.add('loaded');

    if (state.savedData) runMatching(); // auto re-match when both files are present
  } catch (err) {
    setPill(statusEl, 'status-err', '&#10007; failed to load definition: <b>' + escapeHtml(err.message || String(err)) + '</b>');
  } finally { $('#defFileInput').value = ''; } // allow re-selecting the same file later
}

async function handleSavedArmyFile(file) {
  const statusEl = $('#savedStatus');
  try {
    state.savedRawText = await file.text();
    state.savedData = JSON.parse(state.savedRawText);
    if (!Array.isArray(state.savedData.ObjectStates)) throw new Error('ObjectStates array not found — is this a TTS save file?');

    const withDesc = state.savedData.ObjectStates.filter(o => o && getDescText(o).length > 0).length;
    setPill(statusEl, 'status-ok', '&#10003; <b>' + escapeHtml(file.name) + '</b> — ' + state.savedData.ObjectStates.length + ' objects (' + withDesc + ' have a Description field)');

    if (state.abilities && state.abilities.length) runMatching();
  } catch (err) {
    setPill(statusEl, 'status-err', '&#10007; failed to load saved army: <b>' + escapeHtml(err.message || String(err)) + '</b>');
  } finally { $('#savedFileInput').value = ''; }
}

function runMatching() {
  const thresholdPct = Number($('#fuzzyThreshold')?.value ?? 82);
  state.proposals = buildProposals(thresholdPct)
    .sort((a, b) => a.objIndex - b.objIndex || (Number(b.fuzzy) - Number(a.fuzzy)));

  renderResults();
  renderAbilitiesOverview(); // keep the bulk-control / edit panel in sync with current matches
}

function escapeHtml(s) { return String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c])); }

/* ------------------------- results rendering -------------------------- */
const DESC_PREVIEW_CHARS = 160;

function renderResults() {
  const card = $('#results-card');
  const processCard = $('#process-card');
  const tbody = $('#proposalsBody');
  const noMatchesNote = $('#noMatchesNote');
  const summaryEl = $('#matchSummary');

  card.classList.remove('hidden');
  if (state.proposals.length) {
    processCard.classList.remove('hidden');
    noMatchesNote.classList.add('hidden');
    tbody.innerHTML = '';

    let lastObjIndex = -1;
    state.proposals.forEach(p => {
      // object header row when the group changes
      if (p.objIndex !== lastObjIndex) {
        const trH = document.createElement('tr');
        trH.className = 'obj-row';
        th_h(trH, 5).textContent = p.nickname;
        tbody.appendChild(trH);
        lastObjIndex = p.objIndex;
      }

      const tr = document.createElement('tr');
      tr.className = 'proposal-row';
      tr.dataset.id = p.id;

      // checkbox (checked by default) — its state is what Process reads via cb.checked
      td_check(p, tr);

      // object nickname cell — short tag so the row is self-explanatory even when scrolled away from its header
      const tObj = document.createElement('td');
      tObj.className = 'obj-name-cell';
      tObj.textContent = p.nickname;
      tr.appendChild(tObj);

      // ability name (from definition) + fuzzy badge if it was a fuzzy match
      const tAb = document.createElement('td');
      tAb.innerHTML = '<span class="ability-name">' + escapeHtml(p.abilityName) + '</span>';
      if (p.fuzzy) {
        const badge = document.createElement('span');
        badge.className = 'badge-fuzzy';
        badge.textContent = 'fuzzy ~' + Math.round((p.score || 0) * 100) + '%';
        tAb.appendChild(badge);
      }
      tr.appendChild(tAb);

      // matched-as text (what we actually found in the file — may differ from ability name if fuzzy)
      const tMatch = document.createElement('td');
      tMatch.innerHTML = '<span class="mono">' + escapeHtml(p.targetText) + '</span>';
      tr.appendChild(tMatch);

      // description preview with click-to-expand for long texts (shows the ORIGINAL text; edits live in the panel below and apply on Process)
      const tDesc = document.createElement('td');
      const full = p.descText;
      if (full.length > DESC_PREVIEW_CHARS) {
        const span = document.createElement('span');
        span.className = 'desc-preview desc-collapsed';
        span.textContent = truncate(full, DESC_PREVIEW_CHARS);
        span.title = 'Click to expand / collapse the full description — edit it in the "All abilities" panel below';
        let expanded = false;
        span.addEventListener('click', () => {
          if (!expanded) { span.classList.remove('desc-collapsed'); span.style.whiteSpace = 'pre-wrap'; span.textContent = full; }
          else           { span.classList.add('desc-collapsed');  span.style.whiteSpace = '';      span.textContent = truncate(full, DESC_PREVIEW_CHARS); }
          expanded = !expanded;
        });
        tDesc.appendChild(span);
      } else {
        const span2 = document.createElement('span');
        span2.className = 'desc-preview';
        span2.textContent = full;
        tDesc.appendChild(span2);
      }
      tr.appendChild(tDesc);

      tbody.appendChild(tr);
    });

    summaryEl.innerHTML = state.proposals.length + ' match' + (state.proposals.length === 1 ? '' : 'es') +
                          ' across <b>' + new Set(state.proposals.map(p => p.objIndex)).size + '</b> object(s) — all selected by default';
  } else {
    processCard.classList.add('hidden');
    noMatchesNote.classList.remove('hidden');
    tbody.innerHTML = '';
    summaryEl.textContent = 'no matches found';
  }

  $('#statusMessage').textContent = '';
}

function th_h(tr, colSpan) { const th = document.createElement('th'); th.colSpan = colSpan; tr.appendChild(th); return th; }

function td_check(p, tr) {
  const td = document.createElement('td');
  td.className = 'cell-check';
  const cb = document.createElement('input');
  cb.type = 'checkbox';
  cb.checked = true; // default checked as required — Process reads this exact property (cb.checked) when building the work list
  cb.id = p.id + '_cb';
  cb.addEventListener('change', () => { tr.style.opacity = cb.checked ? '' : '.45'; });
  td.appendChild(cb);
  tr.appendChild(td);
}

/* ===================================================================== *
 * ABILITIES OVERVIEW — bulk enable/disable per ability + editable text   *
 * --------------------------------------------------------------------- *
 * One row per unique ability from the roster. Each row has:              *
 *   - "Enable in all units" / "Disable in all units" buttons             *
 *     (check/un-check that ability's checkbox on every matched unit)     *
 *   - an editable description; whatever is typed here is what Process    *
 *     injects. Leaving it empty marks the ability as skipped.            *
 * ===================================================================== */
function renderAbilitiesOverview() {
  const card = $('#abilitiesCard'); if (!card) return;
  const listEl = $('#abilitiesList');
  // only called from runMatching(), i.e. when both files are loaded and abilities exist
card.classList.remove('hidden');
listEl.innerHTML = '';

// sort by usage frequency (most-used first), then alphabetically for stable ordering of ties
  const useCount = name => state.proposals.reduce((n, p) => n + (normKey(p.abilityName) === normKey(name) ? 1 : 0), 0);
const sortedAbilities = [...state.abilities].sort(
    (a, b) => useCount(b.name) - useCount(a.name) || a.name.localeCompare(b.name)
  );

  sortedAbilities.forEach(ability => {
    const key = normKey(ability.name);
    const matches = state.proposals.filter(p => normKey(p.abilityName) === key);

    // ---- row container -------------------------------------------------
    const item = document.createElement('div');
    item.className = 'ability-item';
    item.dataset.key = key;

    // left: name + where it matched (+ edited flag when an override exists)
    const idBlock = document.createElement('div');
    idBlock.className = 'ability-id-block';

    const nm = document.createElement('span');
    nm.className = 'ability-item-name';
    nm.textContent = ability.name;
    idBlock.appendChild(nm);

    const badge = document.createElement('span');
    if (matches.length) {
      badge.className = 'count-badge';
      badge.textContent = matches.length + (matches.length === 1 ? ' unit' : ' units');
    } else {
      badge.className = 'count-badge none';
      badge.textContent = 'not matched in any unit';
    }
    idBlock.appendChild(badge);

    const editedFlag = document.createElement('span');
    editedFlag.className = 'edited-flag hidden';
    editedFlag.textContent = 'edited';
    if (hasOverride(ability.name)) { item.classList.add('is-edited'); editedFlag.classList.remove('hidden'); } // restore flag after re-render (e.g. threshold change)
    idBlock.appendChild(editedFlag);

    item.appendChild(idBlock);

    // middle: editable description — user edit wins over the original definition text on Process
    const ta = document.createElement('textarea');
    ta.className = 'desc-edit';
    ta.rows = 2;
    ta.spellcheck = false;
    ta.placeholder = '(empty → this ability will be skipped when processing)';
    if (hasOverride(ability.name)) {
      state.descOverrides[key] !== undefined && (ta.value = String(state.descOverrides[key])); // '' allowed — means "skip"
    } else {
      ta.value = ability.desc;
    }

    item.appendChild(ta);

    // right: Enable / Disable buttons for ALL units that have this ability
    const btns = document.createElement('div');
    btns.style.display = 'flex';
    btns.style.gap = '.4rem';
    btns.style.flexWrap = 'wrap';

    const btnEnable  = mkMiniBtn(true);
    const btnDisable = mkMiniBtn(false);
    btns.appendChild(btnEnable); btns.appendChild(btnDisable);
    item.appendChild(btns);

    // ---- events ---------------------------------------------------------
    ta.addEventListener('input', () => {
      const v = ta.value;
      if (v.trim() !== '' && v === ability.desc) delete state.descOverrides[key]; // typed back to original → drop override
      else                                       state.descOverrides[key] = v;     // edited OR intentionally emptied ('' = skip on Process)

      const touched = hasOverride(ability.name);
      item.classList.toggle('is-edited', touched);
      editedFlag.classList.toggle('hidden', !touched);
    });

    btnEnable.addEventListener('click',  () => setAbilityInAllUnits(key, true));
    btnDisable.addEventListener('click', () => setAbilityInAllUnits(key, false));

    listEl.appendChild(item);
  });
}

function mkMiniBtn(enable) {
  const b = document.createElement('button');
  b.type = 'button';
  if (enable) {
    b.className = 'btn-mini btn-enable';
    b.innerHTML = '&#9745; Enable in all units';
    b.title = 'Check the checkbox for this ability on every matched unit';
  } else {
    b.className = 'btn-mini btn-disable';
    b.innerHTML = '&#9744; Disable in all units';
    b.title = 'Uncheck the checkbox for this ability on every matched unit';
  }
  return b;
}

/** Check (or uncheck) the proposal checkbox for one ability on EVERY unit it appears on. */
function setAbilityInAllUnits(abilityKey, checked) {
  const key = normKey(String(abilityKey));
  let n = 0;
  state.proposals.forEach(p => {
    if (normKey(p.abilityName) !== key) return; // only this ability's rows — the disabled header checkbox has no id and is never found here

    const cb = document.getElementById(p.id + '_cb');   // proposal checkboxes are <proposalId>_cb
    if (cb && !cb.disabled) {                            // skip anything that isn't a real, enabled row checkbox
      cb.checked = checked;                              // set state directly — no 'change' event fired on purpose…
      const row = document.querySelector('#proposalsBody tr[data-id="' + p.id + '"]');
      if (row) row.style.opacity = checked ? '' : '.45'; // …so keep the visual dimming in sync manually
    }
    n++;
  });

  return n; // number of units affected — handy for future status messages / tests
}

/* ------------------------------ events -------------------------------- */
document.addEventListener('DOMContentLoaded', () => {
  $('#defFileInput').addEventListener('change', e => { const f = e.target.files[0]; if (f) handleDefinitionFile(f); });
  $('#savedFileInput').addEventListener('change', e => { const f = e.target.files[0]; if (f) handleSavedArmyFile(f); });

  // threshold slider — live label + re-match when both files are loaded
  const thrEl = $('#fuzzyThreshold');
  const valEl = $('#thresholdValue');
  function syncThr() {
    valEl.textContent = thrEl.value + '%';
    if (state.abilities?.length && state.savedData) runMatching(); // re-rendering the overview panel keeps any description edits intact via descOverrides
  }
  thrEl.addEventListener('input', syncThr);

  // select all / deselect all — only real proposal checkboxes have ids ending in _cb and are not disabled; they set cb.checked which Process reads back
  $('#selectAllBtn').addEventListener('click', () => {
    document.querySelectorAll('#proposalsBody input[type="checkbox"]').forEach(cb => cb.checked = true);
    document.querySelectorAll('.proposal-row').forEach(r => r.style.opacity = '');
  });

  $('#deselectAllBtn').addEventListener('click', () => {
    document.querySelectorAll('#proposalsBody input[type="checkbox"]').forEach(cb => cb.checked = false);
    document.querySelectorAll('.proposal-row').forEach(r => r.style.opacity = '.45');
  });

  // PROCESS button — the main action: apply ONLY checked proposals (with any description edits), download result file
  $('#processBtn').addEventListener('click', async () => {
    const statusEl = $('#statusMessage');
    if (!state.savedRawText || !state.abilities?.length) { showStatus(statusEl, 'err', 'Load both files first.'); return; }

    // gather ids of the CHECKED proposal rows — cb.checked is what decides whether a row goes into the work list (header checkbox has no id → ignored)
    const checkedIds = new Set();
    document.querySelectorAll('#proposalsBody input[type="checkbox"]').forEach(cb => { if (!cb.disabled && cb.id.endsWith('_cb') && cb.checked === true) checkedIds.add(cb.id.slice(0, -3)); });

    const selected = state.proposals.filter(p => checkedIds.has(p.id));
    if (!selected.length) { showStatus(statusEl, 'err', 'Nothing is checked to inject.'); return; }

    try {
      statusEl.className = 'mono status-message';
      statusEl.textContent = 'Processing… (' + selected.length + ' ability' + (selected.length === 1 ? '' : 'ies') + ')';

      const result = processCheckedProposals(checkedIds); // applies ONLY checked proposals, only to Description fields; uses edited descriptions from the panel above
      if (!result.appliedCount) { showStatus(statusEl, 'err', '&#9888; No changes could be applied — check the console for details.'); return; }

      downloadText('saved-army-with-abilities.json', serializeLikeTts(result.data)); // browser lets user rename on save
      renderPreview(selected);
      if (result.failed.length) { showStatus(statusEl, 'ok', '&#10003; Injected <b>' + result.appliedCount + '</b> description(s). Skipped: ' + escapeHtml(result.failed.join(', ')) + '. Download started — import it back into Tabletop Simulator.'); }
      else                      { showStatus(statusEl, 'ok', '&#10003; Injected <b>' + result.appliedCount + '</b> ability description(s) into the Description field of matched objects. Download started — import it back into Tabletop Simulator.'); }

    } catch (err) {
      console.error(err);
      showStatus(statusEl, 'err', '&#10007; Processing failed: <b>' + escapeHtml(err.message || String(err)) + '</b>');
    }
  });
});

function showStatus(el, kind, htmlOrText) {
  el.className = 'mono status-message ' + (kind === 'ok' ? 'status-ok-text' : 'status-err-text');
  if (/</.test(htmlOrText)) el.innerHTML = htmlOrText; else el.textContent = htmlOrText;
}

/* ------------------------------ preview -------------------------------- */
function renderPreview(selectedProposals) {
  const card = $('#preview-card');
  const listEl = $('#previewList');
  if (!card || !listEl) return;
  card.classList.remove('hidden');
  listEl.innerHTML = '';

  // group by object index so each affected Description is shown once, fully updated (same order as processing)
  const groups = new Map();
  for (const p of selectedProposals) {
    if (!groups.has(p.objIndex)) groups.set(p.objIndex, []);
    groups.get(p.objIndex).push(p);
  }

  // rebuild each object's final Description exactly as processCheckedProposals would have done it — including any description edits from the panel above
  const base = JSON.parse(state.savedRawText);
  for (const [objIdxStr, props] of Array.from(groups.entries()).sort((a, b) => Number(a[0]) - Number(b[0]))) {
    const objIdx = Number(objIdxStr);
    let descText;
    if ('Description' in base.ObjectStates[objIdx]) descText = String(base.ObjectStates[objIdx].Description ?? '');
    else if ('description' in base.ObjectStates[objIdx]) descText = String(base.ObjectStates[objIdx].description ?? '');

    for (const p of props) {
      const d2 = descriptionFor(p); // user edit wins over original; '' means "skip" — same rule as processing uses it
      if (!d2.trim()) continue;     // emptied in the panel → nothing injected, exactly like Process does it
      const u = injectAfter(descText, p.targetText, d2); if (u !== null && u !== descText) descText = u;
    }

    const item = document.createElement('div');
    item.className = 'preview-item';
    const h4 = document.createElement('h4');
    h4.textContent = props[0].nickname + '  —  Description after injection (' + props.length + (props.length === 1 ? ' ability)' : ' abilities)');
    item.appendChild(h4);

    // full updated text; newlines shown as real line breaks here, stored in the file as \n escapes exactly like before
    const pre = document.createElement('pre');
    pre.className = 'desc-preview';
    pre.style.whiteSpace = 'pre-wrap';
    pre.textContent = descText;
    item.appendChild(pre);

    listEl.appendChild(item);
  }
}
