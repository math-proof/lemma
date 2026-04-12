/**
 * Build `.lean` file text from the POST body shape produced by `render.vue` / `lemma.vue`,
 * mirroring the save path in `php/lemma.php` (import filtering matches `lemma.php` try_pattern block).
 */
import { listLemmaTopLevelDirs } from './lemmaSections.mjs';
import { filterImportsByLemmaCode } from './filterImportsByLemmaCode.mjs';
import { detectLemmaImportsFromScanText, stripOpenSectionQualifiers } from './detectLemmaImports.mjs';
import { mergeSyntaxDrivenImports } from './syntaxDrivenImports.mjs';
import { pruneRedundantSyntaxImports } from './importSyntaxDeps.mjs';

/**
 * @param {unknown} val
 * @returns {string[]}
 */
function coerceIndexedStrings(val) {
  if (val == null) return [];
  if (typeof val === 'string') {
    try {
      const p = JSON.parse(val);
      if (Array.isArray(p)) return p.map(String);
    } catch {
      return [val];
    }
    return [val];
  }
  if (Array.isArray(val)) return val.map(String);
  if (typeof val === 'object') {
    return Object.keys(val)
      .filter((k) => /^\d+$/.test(k))
      .sort((a, b) => Number(a) - Number(b))
      .map((k) => val[k])
      .map(String);
  }
  return [];
}

/**
 * @param {unknown} lemma
 * @returns {Record<string, unknown>[]}
 */
function coerceLemmaArray(lemma) {
  if (lemma == null) return [];
  if (Array.isArray(lemma)) return lemma.map((x) => (x && typeof x === 'object' ? x : {}));
  if (typeof lemma === 'object') {
    return Object.keys(lemma)
      .filter((k) => /^\d+$/.test(k))
      .sort((a, b) => Number(a) - Number(b))
      .map((k) => lemma[k])
      .filter((x) => x && typeof x === 'object');
  }
  return [];
}

function indentEachLine(text, prefix = '  ') {
  if (text == null || text === '') return '';
  return String(text)
    .split('\n')
    .map((l) => prefix + l)
    .join('\n');
}

/**
 * Form posts sometimes merge tactics into one line: `rw [a],rw [b]` — invalid Lean.
 * Split at `,` before `rw [` into separate lines (trim + re-indent in caller).
 * @param {string[]} lines
 * @returns {string[]}
 */
function expandCommaRwLines(lines) {
  const out = [];
  for (const ln of lines) {
    const s = String(ln);
    if (/,\s*rw\s*\[/i.test(s)) {
      const bits = s.split(/,(?=\s*rw\s*\[)/i);
      for (const b of bits) {
        const t = b.trim();
        if (t) out.push(t);
      }
    } else {
      out.push(s);
    }
  }
  return out;
}

/**
 * Vue / CodeMirror often post `{ lean: "…" }` per line; `String(x)` would yield `[object Object]`.
 * @param {unknown} x
 */
function proofLineToString(x) {
  if (x == null) return '';
  if (typeof x === 'string') return x;
  if (typeof x === 'object' && x != null && 'lean' in x) return String(/** @type {{ lean: unknown }} */ (x).lean);
  return String(x);
}

/**
 * POST `lemma[n][proof][by][0]`, `[1]`, … parses as an array in Express (`qs` / `body-parser`).
 * `String(array)` would join with commas and corrupt tactics.
 *
 * @param {unknown} byRaw
 * @returns {string}
 */
function normalizeProofByField(byRaw) {
  if (byRaw == null) return '';
  if (typeof byRaw === 'string') return byRaw;
  if (Array.isArray(byRaw)) return byRaw.map(proofLineToString).join('\n');
  return proofLineToString(byRaw);
}

/**
 * @param {unknown} proof
 * @returns {{ kind: 'by' | 'calc' | '', lines: string[] }}
 */
function extractProofLines(proof) {
  if (!proof || typeof proof !== 'object') return { kind: '', lines: [] };
  const o = proof;
  const byRaw = o.by;
  const byStr = normalizeProofByField(byRaw);
  const hasBy = byStr.trim() !== '';

  let calcArr = [];
  const calcRaw = o.calc;
  if (calcRaw != null) {
    if (Array.isArray(calcRaw)) calcArr = calcRaw.map(proofLineToString);
    else if (typeof calcRaw === 'object') {
      calcArr = Object.keys(calcRaw)
        .filter((k) => /^\d+$/.test(k))
        .sort((a, b) => Number(a) - Number(b))
        .map((k) => proofLineToString(calcRaw[k]));
    } else if (typeof calcRaw === 'string' && calcRaw.trim()) calcArr = [calcRaw];
  }
  const hasCalc = calcArr.some((s) => String(s).trim() !== '');

  if (hasBy) return { kind: 'by', lines: byStr.split('\n') };
  if (hasCalc) return { kind: 'calc', lines: calcArr.flatMap((s) => String(s).split('\n')) };
  return { kind: '', lines: [] };
}

/**
 * @param {Record<string, unknown>} L
 */
function buildLemmaBlock(L) {
  const sections = listLemmaTopLevelDirs();

  let comment = '';
  if (L.comment) comment = `/--\n${String(L.comment)}\n-/\n`;

  let attribute = '';
  if (L.attribute) {
    let attr = L.attribute;
    if (typeof attr === 'string') {
      try {
        attr = JSON.parse(attr);
      } catch {
        attr = [];
      }
    }
    if (Array.isArray(attr) && attr.length) attribute = `@[${attr.join(', ')}]\n`;
  }

  const accessibility = L.accessibility ? `${String(L.accessibility)} ` : '';
  const name = String(L.name ?? '');

  const declspecParts = [];
  if (L.instImplicit) declspecParts.push(indentEachLine(String(L.instImplicit)));
  if (L.strictImplicit) declspecParts.push(indentEachLine(String(L.strictImplicit)));
  if (L.implicit) declspecParts.push(indentEachLine(String(L.implicit)));

  const explicit = L.explicit ? String(L.explicit) : '';
  if (explicit) {
    declspecParts.push('-- given');
    declspecParts.push(indentEachLine(explicit));
  }

  const givenArr = coerceIndexedStrings(L.given);
  if (givenArr.length) {
    if (!explicit) declspecParts.push('-- given');
    for (const g of givenArr) declspecParts.push(indentEachLine(g));
  }

  if (L.default) declspecParts.push(indentEachLine(String(L.default)));

  let declspec = declspecParts.join('\n');
  if (declspec) {
    declspec = `\n${declspec.trimEnd()}`;
    if (!declspec.endsWith(':')) declspec += ' :';
  } else {
    declspec = ' :';
  }

  /** PHP: indent `imply` then `detect_lemma` (strips `Section.` when `open`); proof: detect on raw lines then indent. */
  const implyRaw =
    L.imply == null
      ? ''
      : typeof L.imply === 'string'
        ? L.imply
        : typeof L.imply === 'object' && 'lean' in L.imply
          ? String(/** @type {{ lean: unknown }} */ (L.imply).lean)
          : String(L.imply);
  let imply = indentEachLine(implyRaw);
  imply = stripOpenSectionQualifiers(imply, sections);

  const { kind, lines } = extractProofLines(L.proof);
  let proofBody = expandCommaRwLines(lines)
    .map((ln) => stripOpenSectionQualifiers(String(ln), sections))
    .map((ln) => indentEachLine(ln))
    .join('\n');
  proofBody = proofBody.replace(/^\n+/, '').replace(/\n+$/, '');
  proofBody = proofBody.replace(/(?<=\n)\s+\n/g, '');

  // PHP `lemma.php` uses `by`/`calc` only to pick `$proof['by']` vs `$proof['calc']`;
  // it does not print the word `by`/`calc` before the proof lines (the `:= by` lives in imply).
  const proofSection =
    kind === 'by' || kind === 'calc' ? proofBody : '';

  return `${comment}${attribute}${accessibility}lemma ${name}${declspec}
-- imply
${imply}
-- proof
${proofSection}`;
}

/**
 * Same strings PHP pushes to `$lemmaCode` before `try_pattern` (heredoc with imply + proof per lemma).
 * @param {Record<string, unknown>[]} lemmaArr
 */
function buildLemmaCodeForImportFilter(lemmaArr) {
  return lemmaArr.map((L) => buildLemmaBlock(L)).join('\n\n\n');
}

function parseJsonField(raw, fallback) {
  if (raw == null || raw === '') return fallback;
  if (typeof raw !== 'string') return raw;
  try {
    return JSON.parse(raw);
  } catch {
    return fallback;
  }
}

/**
 * @param {Record<string, unknown>} body
 * @returns {Promise<string>}
 */
export async function assembleLeanSourceFromPostBody(body) {
  const sectionSet = new Set(listLemmaTopLevelDirs());

  let imports = parseJsonField(body.imports, []);
  if (!Array.isArray(imports)) imports = [];
  imports = imports.map(String);

  let open = parseJsonField(body.open, []);
  if (!Array.isArray(open)) open = [];

  let set_option = parseJsonField(body.set_option, []);
  if (!Array.isArray(set_option)) set_option = [];

  const defParts = coerceIndexedStrings(body.def).filter((s) => String(s).trim() !== '');

  const lemmaArr = coerceLemmaArray(body.lemma);
  if (lemmaArr.length === 0) {
    throw new Error('Missing lemma fields in POST body');
  }

  const openSectionList = [];
  for (const packages of open) {
    if (Array.isArray(packages)) {
      for (const pkg of packages) {
        if (pkg && sectionSet.has(String(pkg))) openSectionList.push(String(pkg));
      }
    }
  }

  /** PHP `detect_lemma` on imply + proof lines before `array_filter` imports. */
  const sections = listLemmaTopLevelDirs();
  const detectedImports = [];
  const detectedOpen = new Set(openSectionList);
  for (const L of lemmaArr) {
    const implyRaw = L.imply != null ? String(L.imply) : '';
    const implyScan = implyRaw ? indentEachLine(implyRaw) : '';
    const { kind, lines } = extractProofLines(L.proof);
    const proofScan =
      kind === 'by' || kind === 'calc' ? expandCommaRwLines(lines).map((ln) => String(ln)).join('\n') : '';
    const chunk = [implyScan, proofScan].filter(Boolean).join('\n');
    const { imports: addI, sectionsFound } = detectLemmaImportsFromScanText(chunk, sections);
    detectedImports.push(...addI);
    for (const sec of sectionsFound) {
      if (sectionSet.has(sec)) detectedOpen.add(sec);
    }
  }
  imports = [...imports, ...detectedImports];

  const openSectionListForFilter = [...detectedOpen];

  const lemmaCodeForImportFilter = buildLemmaCodeForImportFilter(lemmaArr);
  imports = filterImportsByLemmaCode(imports, lemmaCodeForImportFilter, openSectionListForFilter);

  const uniqImports = [...new Set(imports)].sort();
  if (
    !uniqImports.some((i) => String(i).startsWith('Lemma.')) &&
    !uniqImports.includes('sympy.Basic')
  ) {
    uniqImports.push('sympy.Basic');
  }
  const importLines = uniqImports.map((i) => `import ${i}`);

  const openSection = {};
  for (const imp of uniqImports) {
    const parts = imp.split('.');
    if (parts[0] === 'Lemma' && parts[1]) openSection[parts[1]] = true;
  }

  const openMathlib = [];
  const openVariable = [];
  for (const packages of open) {
    if (Array.isArray(packages)) {
      for (const pkg of packages) {
        if (sectionSet.has(pkg)) openSection[pkg] = true;
        else if (pkg) openMathlib.push(String(pkg));
      }
    } else if (packages && typeof packages === 'object') {
      openVariable.push(packages);
    }
  }

  /**
   * Match `php/std.php` `Text::writelines`: `implode("\n", $leanCode)`.
   * Never push a def chunk that is only newlines (empty `def[*]` fields caused
   * extra blank lines before `@[` when joined with the `\n\n` lemma prefix).
   * @type {string[]}
   */
  const parts = [];
  parts.push(importLines.join('\n'));

  const os = [...Object.keys(openSection), ...openMathlib];
  if (os.length) parts.push(`open ${os.join(' ')}`);

  for (const entity of openVariable) {
    if (!entity || typeof entity !== 'object') continue;
    const ent = Object.entries(entity);
    if (!ent.length) continue;
    const [sec, variables] = ent[0];
    const vars = Array.isArray(variables) ? variables.join(' ') : String(variables);
    parts.push(`open ${sec} (${vars})`);
  }

  for (const option of set_option) {
    if (Array.isArray(option) && option.length > 0) {
      parts.push(`set_option ${option.join(' ')}`);
    }
  }

  if (defParts.length) {
    parts.push(`\n\n${defParts.join('\n\n\n')}`);
  }

  const lemmaCode = lemmaArr.map((L) => buildLemmaBlock(L)).join('\n\n\n');
  parts.push(`\n\n${lemmaCode}`);

  const date = parseJsonField(body.date, {});
  const created =
    date && typeof date === 'object' && date.created != null
      ? String(date.created)
      : new Date().toISOString().slice(0, 10);
  parts.push(`\n\n-- created on ${created}`);
  const updated = new Date().toISOString().slice(0, 10);
  if (updated !== created) parts.push(`-- updated on ${updated}`);
  parts.push('');

  let out = parts
    .join('\n')
    .split('\n')
    .map((line) => line.replace(/\r/g, ''))
    .join('\n');

  /** `php/lemma.php` compile → `$syntax` → `import_syntax` (e.g. `≃` → `stdlib.SEq`). */
  const mergedImports = await mergeSyntaxDrivenImports([...uniqImports], out);
  let finalImports = [...new Set(mergedImports)].sort();
  if (
    !finalImports.some((i) => String(i).startsWith('Lemma.')) &&
    !finalImports.includes('sympy.Basic')
  ) {
    finalImports.push('sympy.Basic');
    finalImports.sort();
  }
  finalImports = await pruneRedundantSyntaxImports(finalImports);
  const newImportBlock = finalImports.map((i) => `import ${i}`).join('\n');
  /** Compare to assembled header (not only `uniqImports`) so merge+prune wins when e.g. `uniq === final` but `parts[0]` was stale. */
  if (parts[0] !== newImportBlock) {
    parts[0] = newImportBlock;
    out = parts
      .join('\n')
      .split('\n')
      .map((line) => line.replace(/\r/g, ''))
      .join('\n');
  }

  return out;
}
