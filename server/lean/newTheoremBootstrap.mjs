/**
 * PHP `php/new.php` mathlib branch: when there is no local `Lemma/…` file, build the
 * `newTheorem` payload from one `mathlib` row (exact `name` = query module).
 */
import { compile, LeanModule } from '../../static/js/parser/lean.js';
import { mathlibRowToLemmaPayload } from './fetchLemmaMysql.mjs';

/**
 * @param {Record<string, unknown>} lemma
 */
function cloneLemmaForNewTheorem(lemma) {
  const imply = lemma.imply && typeof lemma.imply === 'object' ? { ...lemma.imply } : { lean: '', latex: '' };
  const given = Array.isArray(lemma.given)
    ? lemma.given.map((g) => (g && typeof g === 'object' ? { ...g } : g))
    : [];
  return { ...lemma, imply, given };
}

/**
 * @param {unknown} args
 */
function firstVarTokenString(args) {
  if (!Array.isArray(args) || args.length === 0) return '';
  const head = args[0];
  if (head == null) return '';
  return String(head);
}

/**
 * @param {Record<string, unknown>} row — one `SELECT * FROM mathlib` row
 * @param {string} module — dotted name (`dvd_zero`, …)
 * @returns {Record<string, unknown>} `createApp('newTheorem', …)` payload
 */
export function buildNewTheoremCodeFromMathlibRow(row, module) {
  const lemma = cloneLemmaForNewTheorem(mathlibRowToLemmaPayload(/** @type {Record<string, unknown>} */ (row)));
  const imp = /** @type {{ lean?: string; latex?: string }} */ (lemma.imply);
  imp.lean = (imp.lean != null ? String(imp.lean) : '') + ' :=';
  imp.latex = (imp.latex != null ? String(imp.latex) : '') + '\\tag*{ :=}';

  let proof = module;
  /** @type {unknown[][]} */
  const vars = [];

  const defaultRaw = lemma.default;
  const explicit0 =
    defaultRaw != null && String(defaultRaw).trim() !== '' ? String(defaultRaw).trim() : null;
  if (explicit0) {
    delete lemma.default;
    const parser = compile(`${explicit0}\n`);
    if (!(parser instanceof LeanModule)) {
      throw new Error('compile(default) did not return LeanModule');
    }
    vars.push(...parser.parse_vars_default(parser.args));
    lemma.explicit = `${explicit0} :`;
  }

  const giv = lemma.given;
  if (Array.isArray(giv) && giv.length) {
    for (const g of giv) {
      const lean = String(g?.lean ?? '');
      const parser = compile(`${lean}\n`);
      if (!(parser instanceof LeanModule)) {
        throw new Error('compile(given lean) did not return LeanModule');
      }
      vars.push(...parser.parse_vars_default(parser.args));
    }
    if (!lemma.explicit) {
      const last = giv[giv.length - 1];
      last.lean = String(last.lean ?? '') + ' :';
    }
  }

  proof += vars.map((args) => ` ${firstVarTokenString(args)}`).join('');
  lemma.proof = [{ lean: proof }];

  lemma.name = 'main';
  lemma.accessibility = 'private';
  lemma.attribute = ['main'];

  const today = new Date().toISOString().slice(0, 10);
  return {
    imports: [],
    open: [],
    def: [],
    lemma: [lemma],
    error: [],
    date: { created: today },
    name: module,
    module: null,
  };
}
