/**
 * `@[axioms]` reports (`#print axioms`) after the echo sidecar compiles.
 * Allowed Lean axioms are silent. Any other name is a style warning, not a Lean error.
 */

/** The only axiom names `@[path, axioms]` may report. */
export const ALLOWED_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound'];

const ALLOWED = new Set(ALLOWED_AXIOMS);

/**
 * `@[axioms]` info text, or null when the line is not that report.
 * @param {string} info
 * @returns {{ axioms: string[] } | null}
 */
/** A `#print axioms` line with no `file:line:col` prefix. Positioned diagnostics are not this. */
export function isBareAxiomReport(line) {
  const text = String(line ?? '');
  if (/^.+\.lean:\d+:\d+:/.test(text)) return false;
  return /does not depend on any axioms/.test(text) || /depends on axioms:\s*\[/.test(text);
}

/**
 * Read one axiom report starting at `index`, including a list wrapped onto later lines.
 * @param {string[]} lines
 * @param {number} index
 * @param {string} info
 * @returns {{ info: string, next: number }} `next` is the first line not consumed
 */
export function completeAxiomMessage(lines, index, info) {
  let i = index;
  let text = String(info ?? '');
  if (/depends on axioms:\s*\[/.test(text) && !/\]/.test(text)) {
    while (i + 1 < lines.length && !/\]/.test(text)) {
      i += 1;
      text += `\n${lines[i]}`;
    }
  }
  return { info: text, next: i + 1 };
}

/**
 * Lift bare `@[axioms]` reports out of Lean stdout.
 * `lake env lean` prints `'decl' depends on axioms: […]` with no location, so the
 * echo parser used to drop it (or glue it onto the previous diagnostic).
 * `collectAxioms` is transitive: a lemma with no `sorry` still lists `sorryAx`
 * when an imported (or otherwise used) declaration depends on it.
 * @param {string[]} lines
 * @returns {{ rest: string[], reports: string[] }}
 */
export function extractBareAxiomReports(lines) {
  const rest = [];
  const reports = [];
  const src = lines || [];
  for (let i = 0; i < src.length; i++) {
    if (!isBareAxiomReport(src[i])) {
      rest.push(src[i]);
      continue;
    }
    const taken = completeAxiomMessage(src, i, src[i]);
    reports.push(taken.info);
    i = taken.next - 1;
  }
  return { rest, reports };
}

export function parseAxiomReport(info) {
  const text = String(info || '');
  if (/does not depend on any axioms/.test(text)) return { axioms: [] };
  const m = text.match(/depends on axioms:\s*\[([\s\S]*?)\]/);
  if (!m) return null;
  const axioms = m[1]
    .split(',')
    .map((s) => s.trim().replace(/^`+|`+$/g, ''))
    .filter(Boolean);
  return { axioms };
}

/** Names in `axioms` that are not {@link ALLOWED_AXIOMS}, in report order. */
export function unexpectedAxioms(axioms) {
  return (axioms || []).filter((name) => !ALLOWED.has(name));
}

/**
 * Style warning for one axiom report that names something outside the allow-list.
 * @param {{ line?: number, col?: number, code?: string }} loc
 * @param {string[]} extras
 */
export function axiomStyleWarning(loc, extras) {
  const listed = extras.join(', ');
  const allowed = ALLOWED_AXIOMS.join(', ');
  return {
    type: 'warning',
    rule: 'axioms',
    line: loc.line,
    ...(loc.col != null ? { col: loc.col } : {}),
    code: loc.code || '',
    info: `[axioms] unexpected axioms: ${listed} (allowed: ${allowed})`,
  };
}

/**
 * Pull `@[axioms]` info out of Lean diagnostics.
 * Allowed-only and empty reports disappear. Extra names become `code.warning` entries.
 * @param {{ line?: number, col?: number, code?: string, info?: string }[]} errors
 * @returns {{ errors: typeof errors, warnings: object[] }}
 */
export function splitAxiomReports(errors) {
  const rest = [];
  const warnings = [];
  for (const err of errors || []) {
    const report = parseAxiomReport(err?.info);
    if (!report) {
      rest.push(err);
      continue;
    }
    const extras = unexpectedAxioms(report.axioms);
    if (extras.length) warnings.push(axiomStyleWarning(err, extras));
  }
  return { errors: rest, warnings };
}
