/**
 * Ports `php/lemma.php` `detect_lemma` qualified branch (lines 143–161):
 * - scan for `Section.Name1…` → add `Lemma.<resolved>` imports;
 * - strip `Section.` prefixes (`preg_replace` line 163) so `open Section` allows short names in output.
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
 * @param {string} text imply + proof lines (same sources PHP passes to `detect_lemma`)
 * @param {string[]} sections `listLemmaTopLevelDirs()`
 * @returns {{ imports: string[]; sectionsFound: string[] }} `Lemma.*` to merge + section roots (for `open_section` like PHP)
 */
export function detectLemmaImportsFromScanText(text, sections) {
  if (!text || !sections.length) return { imports: [], sectionsFound: [] };
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
