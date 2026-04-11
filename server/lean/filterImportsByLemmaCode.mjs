/**
 * Ports `php/lemma.php` (≈313–445) + `try_pattern`, `parseInfixSegments`, `Not` from `php/parser/lean.php`
 * so Node save keeps only imports referenced in proof bodies (same as PHP POST save).
 */
import { parseInfixSegments, Not, tokensToModule } from './moduleResolve.mjs';

/**
 * @param {(string | string[])[]} tokens
 * @param {string} lemmaCode
 */
function tryPattern(tokens, lemmaCode) {
  let imp;
  if (tokens.length && Array.isArray(tokens[0])) {
    imp = tokensToModule(tokens, null);
  } else {
    imp = /** @type {string[]} */ (tokens).join('.');
  }
  const escaped = imp.replace(/\./g, '\\.');
  const suffix = String.raw`(?!\.(?:of\.|[A-Z][\w'!₀-₉]*))`;
  const re = new RegExp(`\\b${escaped}${suffix}`, 'u');
  return re.test(lemmaCode);
}

/**
 * @param {string[]} imports
 * @param {string} lemmaCode
 * @param {string[]} openSectionList
 * @returns {string[]}
 */
export function filterImportsByLemmaCode(imports, lemmaCode, openSectionList) {
  const openSet = new Set(openSectionList.map(String));

  return imports.filter((importLine) => {
    /** @type {string} */
    let section = '';
    const tokens = importLine.split('.');

    switch (tokens[0]) {
      case 'Lemma': {
        tokens.shift();
        section = tokens[0];
        if (openSet.has(section)) tokens.shift();
        break;
      }
      case 'sympy':
        if (tokens[1] === 'Basic') return false;
        return true;
      case 'stdlib':
      case 'Mathlib':
        return true;
      default:
        break;
    }

    if (tryPattern(tokens, lemmaCode)) return true;

    const [section2, segment] = parseInfixSegments(tokens, section || null);
    section = section2;

    switch (tokens[1]) {
      case 'eq':
      case 'as':
      case 'ne': {
        const t = [...tokens];
        [t[0], t[2]] = [t[2], t[0]];
        if (tryPattern(t, lemmaCode)) return true;
        break;
      }
      case 'is': {
        const indexOf = tokens.indexOf('of');
        if (indexOf !== -1) {
          const t = [...tokens];
          t[1] = 'of';
          t.splice(indexOf, 1);
          if (tryPattern(t, lemmaCode)) return true;
          [t[0], t[2]] = [t[2], t[0]];
          if (tryPattern(t, lemmaCode)) return true;
          const m = t[0].match(/^([SH]?Eq|Iff)(?!_)(.+)/);
          if (m) {
            t[0] = `${m[1]}_${m[2]}`;
            if (tryPattern(t, lemmaCode)) return true;
          }
          if (indexOf === 3) {
            t[0] = Not(t[0]);
            t[2] = Not(t[2]);
            if (tryPattern(t, lemmaCode)) return true;
            [t[0], t[2]] = [t[2], t[0]];
            if (tryPattern(t, lemmaCode)) return true;
          }
        } else {
          const t = [...tokens];
          t[1] = 'of';
          if (tryPattern(t, lemmaCode)) return true;
          [t[0], t[2]] = [t[2], t[0]];
          if (tryPattern(t, lemmaCode)) return true;
          if (tokens.length === 3) {
            const t2 = [...tokens];
            t2[0] = Not(t2[0]);
            t2[2] = Not(t2[2]);
            if (tryPattern(t2, lemmaCode)) return true;
            [t2[0], t2[2]] = [t2[2], t2[0]];
            if (tryPattern(t2, lemmaCode)) return true;
          }
          t[1] = 'is';
          if (tryPattern(t, lemmaCode)) return true;
        }
        break;
      }
      case 'of': {
        const t_ = [...tokens];
        let m = t_[0].match(/^([SH]?Eq|Iff)_(.+)/);
        if (m) t_[0] = m[1] + m[2];
        else if ((m = t_[0].match(/^([SH]?Eq|Iff)(.+)/))) t_[0] = `${m[1]}_${m[2]}`;
        else break;
        if (tryPattern(t_, lemmaCode)) return true;
        for (let i = 2; i < tokens.length; i++) {
          const tokensCopy = tokens.slice(2).map(String);
          tokensCopy[i - 2] = String(Not(tokens[0]));
          const candidate = [String(Not(tokens[i])), 'of', ...tokensCopy];
          if (tryPattern(candidate, lemmaCode)) return true;
        }
        break;
      }
      default: {
        if (tokens[1] === undefined || tokens[1] === null) {
          const t = [...tokens];
          let m = t[0].match(/^([SH]?Eq|Iff)_(.+)/);
          if (m) t[0] = m[1] + m[2];
          else if ((m = t[0].match(/^([SH]?Eq|Iff)(.+)/))) t[0] = `${m[1]}_${m[2]}`;
          else break;
          if (tryPattern(t, lemmaCode)) return true;
        } else if (
          segment.length === 3 &&
          segment[1].length === 1 &&
          segment[1][0] === 'is'
        ) {
          const seg = segment.map((r) => [...r]);
          [seg[0], seg[2]] = [seg[2], seg[0]];
          seg[1] = ['of'];
          if (tryPattern(seg, lemmaCode)) return true;
        } else {
          return false;
        }
      }
    }
    return false;
  });
}
