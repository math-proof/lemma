/**
 * Ports `php/lemma.php` `detect_lemma` (lines 152–203):
 * - qualified: `Section.Name1…` → add `Lemma.<resolved>` imports;
 * - same pass strips `Section.` prefixes (line 163) from a scratch copy for the next step;
 * - unqualified: chains not starting with a section (e.g. `SEq.of.SEqDataS.Eq` under `open Tensor`)
 *   → try `Lemma.<section>.<chain>` for each top-level `Lemma/` folder (`module_exists` in PHP).
 */
import { moduleToLeanPath, fileExists } from './modulePath.mjs';
import { resolveMissingModuleRedirect } from './moduleResolve.mjs';

/** Same token tail as PHP `$term` in `lemma.php`. */
const TERM =
  "(?:[A-Z][\\w'!₀-₉]*|(?:of|is|et|ou|to|eq|ne|gt|lt|ge|le|in|as|dvd|sub|sup)(?=\\.))";

/**
 * @param {string} name top-level `Lemma/` directory name
 */
function sectionRegexFragment(name) {
  switch (name) {
    case 'List':
      return 'List(?!\\.Vector)';
    case 'Finset':
      return 'Finset(?!\\.Nonempty)';
    case 'Tensor':
      return 'Tensor(?!\\.T\\b)';
    case 'Hyperreal':
      return 'Hyperreal(?!\\.Infinite(?:Pos|Neg)?(?!\\.)\\b)';
    default:
      return name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  }
}

/**
 * @param {string[]} sections from `listLemmaTopLevelDirs()`
 */
function buildSectionRegex(sections) {
  const inner = sections.map(sectionRegexFragment).join('|');
  return `(?:${inner})(?=[\\.][A-Z])`;
}

/**
 * @param {string} dotted e.g. `List.GetRotate.eq.Get.of.Lt.GtLength`
 * @returns {string | null} canonical dotted module if `Lemma/<path>.lean` exists
 */
function resolveModuleOnDisk(dotted) {
  const p = moduleToLeanPath(dotted);
  if (p && fileExists(p)) return dotted;
  const canon = resolveMissingModuleRedirect(dotted);
  if (canon) {
    const p2 = moduleToLeanPath(canon);
    if (p2 && fileExists(p2)) return canon;
  }
  return null;
}

/**
 * PHP `detect_lemma` line 173: skip adding if some `Lemma.<section>.<lemmaName>` already exists.
 * @param {string[]} imports `Lemma.*` strings
 * @param {string} lemmaName first capture from the unqualified regex (dotted chain)
 */
function importAlreadyCoversLemmaName(imports, lemmaName) {
  const escaped = lemmaName.replace(/\\/g, '\\\\').replace(/\./g, '\\.');
  const re = new RegExp(`^Lemma\\.\\w+\\.${escaped}$`);
  return imports.some((imp) => re.test(imp));
}

/**
 * @param {string} text imply + proof lines (same sources PHP passes to `detect_lemma`)
 * @param {string[]} sections `listLemmaTopLevelDirs()`
 * @param {string[]} [existingImports] PHP `$imports` already present when `detect_lemma` runs
 * @returns {{ imports: string[]; sectionsFound: string[] }} `Lemma.*` to merge + section roots (for `open_section` like PHP)
 */
export function detectLemmaImportsFromScanText(text, sections, existingImports = []) {
  if (!text || !sections.length) return { imports: [], sectionsFound: [] };
  const existing = (existingImports ?? []).map(String);
  const sectionRe = buildSectionRegex(sections);
  const re = new RegExp(`\\b(${sectionRe})((?:\\.${TERM})+)\\b`, 'gu');
  /** @type {Map<string, string>} */
  const byKey = new Map();
  /** @type {Set<string>} */
  const sectionsFound = new Set();
  let m;
  while ((m = re.exec(text)) !== null) {
    const candidate = m[1] + m[2];
    const resolved = resolveModuleOnDisk(candidate);
    if (resolved) {
      byKey.set(resolved, `Lemma.${resolved}`);
      sectionsFound.add(m[1]);
    }
  }
  const importsSoFarFor = () => [...new Set([...existing, ...byKey.values()])];

  // PHP line 163: strip `Tensor.` / `List.` … when followed by a `$term`, so short names match below.
  const stripSectionPrefix = new RegExp(`\\b(?<!@)(${sectionRe})\\.(?=${TERM})`, 'gu');
  const forUnqual = text.replace(stripSectionPrefix, '');
  const unqualRe = new RegExp(
    `\\b(?!${sectionRe})(${TERM}(?:\\.${TERM})*)((?:\\.[a-z_]+)*)(?=\\b[^.]|$)`,
    'gu'
  );
  for (const um of forUnqual.matchAll(unqualRe)) {
    const lemmaName = um[1];
    const submodule = um[2] ?? '';
    if (submodule === '.symm' && lemmaName === 'Eq') continue;

    const importsSoFar = importsSoFarFor();
    if (importAlreadyCoversLemmaName(importsSoFar, lemmaName)) continue;

    /** @type {{ hit: boolean; section: string; resolved: string; lemmaImport: string }[]} */
    const exists = [];
    for (const section of sections) {
      const dotted = `${section}.${lemmaName}`;
      const resolved = resolveModuleOnDisk(dotted);
      if (resolved) {
        const lemmaImport = `Lemma.${resolved}`;
        exists.push({
          hit: importsSoFar.includes(lemmaImport),
          section,
          resolved,
          lemmaImport,
        });
      }
    }
    if (!exists.length) continue;

    const firstHit = exists.find((e) => e.hit);
    if (firstHit) {
      sectionsFound.add(firstHit.section);
      continue;
    }

    const pick = exists[0];
    byKey.set(pick.resolved, pick.lemmaImport);
    sectionsFound.add(pick.section);
  }

  return { imports: [...byKey.values()], sectionsFound: [...sectionsFound] };
}

/**
 * Same as PHP `detect_lemma` line 163: remove `Section.` when `Section` is a lemma package and the
 * next token matches `$term` (skip when `@` immediately precedes the section, e.g. attributes).
 * @param {string} text
 * @param {string[]} sections `listLemmaTopLevelDirs()`
 */
export function stripOpenSectionQualifiers(text, sections) {
  if (!text || !sections.length) return text;
  const sectionRe = buildSectionRegex(sections);
  const re = new RegExp(`\\b(?<!@)(${sectionRe})\\.(?=${TERM})`, 'gu');
  return text.replace(re, '');
}
