/**
 * When `Lemma/<module>.lean` is missing, rewrite dotted modules (of/is, eq swaps,
 * Not/comm, etc.) to match legacy `index.php` (lines 84–332) and return a canonical module for redirect.
 */
import path from 'path';
import fs from 'fs';
import { REPO_ROOT, moduleToLeanPath } from './modulePath.mjs';

/** @param {string} op */
export function isInfixOperator(op) {
  return ['eq', 'is', 'as', 'ne', 'lt', 'le', 'gt', 'ge', 'in', 'ou', 'et'].includes(op);
}

/** @param {string} op */
function isSymmOperator(op) {
  return ['eq', 'is', 'as', 'ne'].includes(op);
}

/** @param {string} s0 @param {string} s */
function transformExpr(s0, s) {
  if (s0 === '_') return s;
  if (/^[A-Z]$/.test(s0)) {
    if (/^[a-zA-Z0-9'!₀-₉]+?S/.test(s)) {
      return s0 + s;
    }
  }
  return `_${s0}${s}`;
}

/** @param {string} s */
function transformPrefix(s) {
  let m = s.match(/^(Eq|Ne|Or)(.)(.*)$/);
  if (m) {
    const [, prefix, s2, rest] = m;
    return prefix + transformExpr(s2, rest);
  }
  m = s.match(/^([SH]Eq)(.)(.*)$/) || s.match(/^(Iff|And)(.)(.*)$/);
  if (m) {
    const [, prefix, s3, rest] = m;
    return prefix + transformExpr(s3, rest);
  }
  m = s.match(/^(L|G)(t|e)(.)(.*)$/);
  if (m) {
    const [, s0, s1, s2, rest] = m;
    const newS0 = s0 === 'L' ? 'G' : 'L';
    return newS0 + s1 + transformExpr(s2, rest);
  }
  m = s.match(/^(L|G)(t|e)$/);
  if (m) {
    const [, s0, s1] = m;
    const newS0 = s0 === 'L' ? 'G' : 'L';
    return newS0 + s1;
  }
  return s;
}

/**
 * @param {string[]} list
 * @param {string | null} [sectionIn]
 * @returns {[string, string[][]]}
 */
export function parseInfixSegments(list, sectionIn = null) {
  let section = sectionIn;
  let rest = list;
  if (!section) {
    section = list[0];
    rest = list.slice(1);
  }
  const n = rest.length;
  if (n === 0) return [section, []];
  if (n === 1) return [section, [[rest[0]]]];

  /** @type {string[][]} */
  const result = [];
  let i = 0;
  while (i < n) {
    if (i + 2 >= n) {
      for (; i < n; i++) result.push([rest[i]]);
      break;
    }
    const x = rest[i];
    const op = rest[i + 1];
    const y = rest[i + 2];
    if (isInfixOperator(op)) {
      result.push([x, op, y]);
      i += 3;
    } else {
      result.push([x]);
      ++i;
    }
  }
  return [section, result];
}

/** @param {string | string[]} token */
export function Not(token) {
  if (typeof token === 'string') {
    if (token.startsWith('Not')) return token.slice(3);
    if (token.startsWith('Eq')) return `Ne${token.slice(2)}`;
    if (token.startsWith('Ne')) return `Eq${token.slice(2)}`;
    return `Not${token}`;
  }
  if (Array.isArray(token)) {
    if (token.length === 1) return [Not(token[0])];
    return token;
  }
  return token;
}

/** @param {string[]} arr @param {number} index @param {string} value */
function arrayInsert(arr, index, value) {
  /** @type {(string | string[])[]} */
  const newArray = [value];
  if (index < arr.length) {
    newArray.push(arr[index]);
  }
  arr.splice(index, 1, ...newArray);
}

/**
 * `Tensor.SEq.of.SEqDataS.Eq` → `Tensor.SEq.is.SEqDataS.of.Eq` when that file exists (PHP `index.php`
 * `array_insert` after `tokens[2] = 'is'` when `of` is not parsed as infix — `is_infix_operator` omits `of`).
 * @param {string[]} tokens dotted module split, e.g. `Tensor.SEq.of.SEqDataS.Eq`
 * @returns {string | null}
 */
function tryOfIsOfFileRewrite(tokens) {
  if (tokens.length < 5 || tokens[2] !== 'of') return null;
  const t = [...tokens];
  t[2] = 'is';
  if (t.length > 4) arrayInsert(t, 4, 'of');
  const m = t.join('.');
  const p = moduleToLeanPath(m);
  return p && fs.existsSync(p) ? m : null;
}

/**
 * Dotted module from `parseInfixSegments` rows (matches PHP `tokens_to_module`).
 * @param {(string | string[])[]} segment
 * @param {string | null} [section]
 */
export function tokensToModule(segment, section) {
  const body = segment
    .map((t) => (Array.isArray(t) ? t.join('.') : String(t)))
    .join('.');
  return section ? `${section}.${body}` : body;
}

/** @param {string[][]} segment @param {string | null} section */
function moduleToLeanFromSegment(segment, section) {
  const dotted = tokensToModule(segment, section);
  return moduleToLeanPath(dotted);
}

/**
 * If `Lemma/<module>.lean` is missing, apply the same rewrites as legacy `index.php`.
 * @param {string} moduleDot
 * @param {string} [repoRoot]
 * @returns {string | null} canonical module to redirect to, or null if no rewrite applies
 */
export function resolveMissingModuleRedirect(moduleDot, repoRoot = REPO_ROOT) {
  const module = String(moduleDot).trim().replace(/\//g, '.');
  if (!module) return null;

  const title = module.replace(/\./g, '/');
  const pathInfo = path.join(repoRoot, 'Lemma', ...title.split('/').filter(Boolean));

  if (pathInfo.endsWith('/') || pathInfo.endsWith(path.sep)) {
    return null;
  }

  let leanFile = `${pathInfo}.lean`;
  if (fs.existsSync(leanFile)) {
    return null;
  }

  if (fs.existsSync(pathInfo) && fs.statSync(pathInfo).isDirectory()) {
    return null;
  }

  const parentLean = `${path.dirname(leanFile)}.lean`;
  if (fs.existsSync(parentLean) && fs.statSync(parentLean).isFile()) {
    const lastDot = module.lastIndexOf('.');
    if (lastDot === -1) return null;
    return `${module.slice(0, lastDot)}#${module.slice(lastDot + 1)}`;
  }

  /** @type {string[]} */
  let tokens = module.split('.');
  const parsed = parseInfixSegments(tokens);
  const section = parsed[0];
  /** @type {string[][]} */
  let segment = parsed[1].map((row) => [...row]);

  let leanFileFlag = leanFile;
  let index = tokens.indexOf('of');

  if (index !== -1) {
    if (segment[1] && segment[1].length === 1) {
      const mid = segment[1][0];
      switch (mid) {
        case 'is': {
          index = tokens.indexOf('of');
          if (index === -1) {
            const tokens_ = [...tokens];
            tokens_[1] = transformPrefix(tokens_[1]);
            tokens_[3] = transformPrefix(tokens_[3]);
            let m = tokens_.join('.');
            const p = moduleToLeanPath(m);
            if (p && fs.existsSync(p)) return m;
            tokens = [tokens[0], ...tokens.slice(3), 'is', tokens[1]];
          } else {
            let m1 = tokens[1].match(/^([SH]?Eq|Iff)_(.+)/);
            if (m1) tokens[1] = m1[1] + m1[2];
            tokens = [
              tokens[0],
              ...tokens.slice(3, index - 3),
              'is',
              tokens[1],
              ...tokens.slice(index),
            ];
          }
          break;
        }
        case 'eq':
        case 'as':
        case 'ne': {
          const tmp = tokens[1];
          tokens[1] = tokens[3];
          tokens[3] = tmp;
          break;
        }
        case 'of': {
          const first = segment[0];
          if (first.length === 1) {
            const mEq = first[0].match(/^([SH]?Eq|Iff)_(.+)/);
            if (mEq) {
              tokens[1] = mEq[1] + mEq[2];
              let m = tokens.join('.');
              const p = moduleToLeanPath(m);
              if (!p || !fs.existsSync(p)) {
                tokens[1] = first[0];
                tokens[2] = 'is';
                if (tokens.length > 4) arrayInsert(tokens, 4, 'of');
              }
            } else {
              if (tokens.length === 5) {
                const tokens_ = [...tokens];
                tokens_[1] = transformPrefix(tokens_[1]);
                tokens_[3] = transformPrefix(tokens_[3]);
                tokens_[4] = transformPrefix(tokens_[4]);
                const m = tokens_.join('.');
                const p = moduleToLeanPath(m);
                if (p && fs.existsSync(p)) return m;
              }
              let hit = false;
              for (let i = 2; i < segment.length; i++) {
                const segment_ = segment.map((r) => [...r]);
                segment_[0] = /** @type {string[][]} */ (Not(segment_[i]));
                segment_[i] = /** @type {string[][]} */ (Not(first));
                const p = moduleToLeanFromSegment(segment_, section);
                if (p && fs.existsSync(p)) {
                  hit = true;
                  segment = segment_;
                  break;
                }
              }
              if (!hit && segment[1]) {
                const flatAlt = tryOfIsOfFileRewrite(tokens);
                if (flatAlt) return flatAlt;
                segment[1][0] = 'is';
              }
            }
          } else if (first.length === 3 && isInfixOperator(first[1])) {
            // (e.g. `Nat.AddSub.eq.SubAdd.of.Ge` → `Nat.SubAdd.eq.AddSub.of.Ge`).
            const segment_ = segment.map((r) => [...r]);
            segment_[0] = [first[2], first[1], first[0]];
            const p = moduleToLeanFromSegment(segment_, section);
            if (p && fs.existsSync(p)) {
              segment = segment_;
            } else if (segment[1]) {
              segment[1][0] = 'is';
            }
          }
          break;
        }
        default: {
          const firstT = tokens[1];
          let m = firstT.match(/^(S?Eq)_([\w'!₀-₉]+)$/);
          if (m) tokens[1] = m[1] + m[2];
          else if ((index = tokens.indexOf('of')) !== -1) tokens[index] = 'is';
          else if ((index = tokens.indexOf('is')) !== -1) {
            const sec = tokens[0];
            const first = tokens.slice(1, index);
            const second = tokens.slice(index + 1);
            tokens = [sec, ...second, 'is', ...first];
          } else leanFileFlag = '';
          break;
        }
      }
    }
  } else {
    if (segment.length > 1 && segment[1] && segment[1].length === 1) {
      const mid = segment[1][0];
      switch (mid) {
        case 'is': {
          index = tokens.indexOf('of');
          if (index === -1) {
            const s0 = segment[0];
            const s2 = segment[2];
            segment[0] = s2;
            segment[2] = s0;
            let m = tokensToModule(segment, section);
            const p = moduleToLeanPath(m);
            if (p && fs.existsSync(p)) return m;
            tokens = [tokens[0], ...tokens.slice(3), 'is', tokens[1]];
          } else {
            let m1 = tokens[1].match(/^([SH]?Eq|Iff)_(.+)/);
            if (m1) tokens[1] = m1[1] + m1[2];
            tokens = [
              tokens[0],
              ...tokens.slice(3, index - 3),
              'is',
              tokens[1],
              ...tokens.slice(index),
            ];
          }
          break;
        }
        case 'eq':
        case 'as':
        case 'ne': {
          const tmp = tokens[1];
          tokens[1] = tokens[3];
          tokens[3] = tmp;
          break;
        }
        case 'of': {
          const first = tokens[1];
          const mEq = first.match(/^([SH]?Eq|Iff)_(.+)/);
          if (mEq) {
            tokens[1] = mEq[1] + mEq[2];
            let m = tokens.join('.');
            const p = moduleToLeanPath(m);
            if (!p || !fs.existsSync(p)) {
              tokens[1] = first;
              tokens[2] = 'is';
              if (tokens.length > 4) arrayInsert(tokens, 4, 'of');
            }
          } else {
            if (tokens.length === 5) {
              const tokens_ = [...tokens];
              tokens_[1] = transformPrefix(tokens_[1]);
              tokens_[3] = transformPrefix(tokens_[3]);
              tokens_[4] = transformPrefix(tokens_[4]);
              const m = tokens_.join('.');
              const p = moduleToLeanPath(m);
              if (p && fs.existsSync(p)) return m;
            }
            {
              const flatAlt = tryOfIsOfFileRewrite(tokens);
              if (flatAlt) return flatAlt;
            }
            tokens[2] = 'is';
          }
          break;
        }
        default: {
          const firstT = tokens[1];
          let mm = firstT.match(/^(S?Eq)_([\w'!₀-₉]+)$/);
          if (mm) tokens[1] = mm[1] + mm[2];
          else if ((index = tokens.indexOf('of')) !== -1) tokens[index] = 'is';
          else if ((index = tokens.indexOf('is')) !== -1) {
            const sec = tokens[0];
            const first = tokens.slice(1, index);
            const second = tokens.slice(index + 1);
            tokens = [sec, ...second, 'is', ...first];
          } else leanFileFlag = '';
          break;
        }
      }
    } else {
      const first = segment[0];
      if (first.length === 1) {
        let mm = first[0].match(/^(S?Eq)_([\w'!₀-₉]+)$/);
        if (mm) tokens[1] = mm[1] + mm[2];
      } else if (first.length === 3 && isSymmOperator(first[1])) {
        let segment_ = segment.map((r) => [...r]);
        segment_[0] = [first[2], first[1], first[0]];
        let p = moduleToLeanFromSegment(segment_, section);
        if (p && fs.existsSync(p)) {
          segment = segment_;
        } else {
          let f = [...segment_[0]];
          f[0] = transformPrefix(f[0]);
          f[2] = transformPrefix(f[2]);
          segment_[0] = f;
          p = moduleToLeanFromSegment(segment_, section);
          if (p && fs.existsSync(p)) {
            segment = segment_;
          } else {
            segment_[0] = [f[2], f[1], f[0]];
            p = moduleToLeanFromSegment(segment_, section);
            if (p && fs.existsSync(p)) segment = segment_;
          }
        }
      } else {
        let mm = first.join('.').match(/^(S?Eq)_([\w'!₀-₉]+)$/);
        if (mm) tokens[1] = mm[1] + mm[2];
        else if ((index = tokens.indexOf('of')) !== -1) tokens[index] = 'is';
        else if ((index = tokens.indexOf('is')) !== -1) {
          const sec = tokens[0];
          const fr = tokens.slice(1, index);
          const second = tokens.slice(index + 1);
          tokens = [sec, ...second, 'is', ...fr];
        } else leanFileFlag = '';
      }
    }
  }

  if (leanFileFlag) {
    const out = tokensToModule(segment, section);
    if (out !== module) {
      const p = moduleToLeanPath(out);
      if (p && fs.existsSync(p)) return out;
    }
  }

  return null;
}

/**
 * Swaps the first infix relation in the parsed module (same rewrite as commutative `@[main, comm]` paths).
 * `imports` in MySQL may use either spelling; reverse hierarchy must match both.
 * @param {string} moduleDot
 * @returns {string | null} alternate dotted module, or null if not applicable / unchanged
 */
export function commutativeImportAlias(moduleDot) {
  const module = String(moduleDot).trim().replace(/\//g, '.');
  if (!module) return null;
  const tokens = module.split('.');
  const parsed = parseInfixSegments(tokens);
  const section = parsed[0];
  /** @type {string[][]} */
  const segment = parsed[1].map((row) => [...row]);
  const first = segment[0];
  if (!first || first.length !== 3 || !isInfixOperator(first[1])) return null;
  const segment_ = segment.map((r) => [...r]);
  segment_[0] = [first[2], first[1], first[0]];
  const swapped = tokensToModule(segment_, section);
  return swapped === module ? null : swapped;
}
