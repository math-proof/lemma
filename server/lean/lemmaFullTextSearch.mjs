/**
 * Full-text search over Lemma/ (all .lean files; skips .echo.lean), matching php/search.php grep.
 */
import fs from 'fs';
import path from 'path';
import { REPO_ROOT, leanPathToModule } from './modulePath.mjs';

/** @param {string} s */
function escapeRegExp(s) {
  return s.replace(/[\\^$.*+?()[\]{}|]/g, '\\$&');
}

/**
 * @param {string} query
 * @param {boolean} caseSensitive
 * @param {boolean} wholeWord
 * @param {boolean} regularExpression
 * @returns {((line: string) => boolean) | null}
 */
function buildLineMatcher(query, caseSensitive, wholeWord, regularExpression) {
  if (query == null || query === '') return null;
  const flags = caseSensitive ? '' : 'i';

  try {
    if (wholeWord && regularExpression) {
      const re = new RegExp(`\\b${query}\\b`, flags);
      return (line) => {
        re.lastIndex = 0;
        return re.test(line);
      };
    }
    if (wholeWord) {
      const re = new RegExp(`\\b${escapeRegExp(query)}\\b`, flags);
      return (line) => {
        re.lastIndex = 0;
        return re.test(line);
      };
    }
    if (regularExpression) {
      const re = new RegExp(query, flags);
      return (line) => {
        re.lastIndex = 0;
        return re.test(line);
      };
    }
  } catch {
    return null;
  }

  if (caseSensitive) {
    return (line) => line.includes(query);
  }
  const q = query.toLowerCase();
  return (line) => line.toLowerCase().includes(q);
}

/**
 * @param {string} lemmaRoot
 * @returns {Generator<string, void, void>}
 */
function* iterLeanFiles(lemmaRoot) {
  /** @param {string} dir */
  function* walk(dir) {
    let entries;
    try {
      entries = fs.readdirSync(dir, { withFileTypes: true });
    } catch {
      return;
    }
    entries.sort((a, b) =>
      a.name.localeCompare(b.name, undefined, { sensitivity: 'base' })
    );
    for (const ent of entries) {
      const full = path.join(dir, ent.name);
      if (ent.isDirectory()) {
        yield* walk(full);
      } else if (
        ent.name.endsWith('.lean') &&
        !ent.name.endsWith('.echo.lean')
      ) {
        yield full;
      }
    }
  }
  yield* walk(lemmaRoot);
}

/**
 * @param {{
 *   query: string;
 *   caseSensitive: boolean;
 *   wholeWord: boolean;
 *   regularExpression: boolean;
 *   limit: number;
 *   repoRoot?: string;
 * }} opts
 * @returns {{ module: string; line: number; text: string }[]}
 */
export function searchLemmaFullText(opts) {
  const {
    query,
    caseSensitive,
    wholeWord,
    regularExpression,
    limit,
    repoRoot = REPO_ROOT,
  } = opts;

  const matcher = buildLineMatcher(
    query,
    caseSensitive,
    wholeWord,
    regularExpression
  );
  if (!matcher) return [];

  const lemmaRoot = path.join(repoRoot, 'Lemma');
  if (!fs.existsSync(lemmaRoot)) return [];

  /** @type {{ module: string; line: number; text: string }[]} */
  const results = [];

  for (const absPath of iterLeanFiles(lemmaRoot)) {
    const mod = leanPathToModule(absPath, repoRoot);
    if (!mod) continue;

    let content;
    try {
      content = fs.readFileSync(absPath, 'utf8');
    } catch {
      continue;
    }

    const lines = content.split(/\r?\n/);
    for (let i = 0; i < lines.length; i++) {
      if (matcher(lines[i])) {
        results.push({
          module: mod,
          line: i + 1,
          text: lines[i],
        });
        if (results.length >= limit) return results;
      }
    }
  }

  return results;
}
