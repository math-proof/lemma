/**
 * Lemma linter: the mechanically checkable style rules of `AGENTS.md` as compiler WARNINGS (never errors).
 *
 * `lintLean(source, opts)` → warnings `{ type: 'warning', rule, line, col, code, info }`, sorted by line.
 * `info` reads `[rule-id] <what to change> (AGENTS.md: "<rule>")`.
 * Warnings never change a lemma's status, `mjs/run.mjs`'s exit code, or the database row (`render2vue.mjs` puts them
 * in `code.warning`, which is not saved).
 *
 * Every rule runs on the comment / string-blanked source (see `scan.mjs`: the lean.js tree has no source positions).
 */
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { listLemmaTopLevelDirs } from '../lemmaSections.mjs';
import { prepare, findDecls } from './scan.mjs';
import { scanImportsAndOpens, openSection, openUnusedAndDuplicate, openPrefix, attrDocstring, dates } from './headerRules.mjs';
import { signatureRules } from './signatureRules.mjs';
import { indentRules, proofRules, underscoreNameRule } from './proofRules.mjs';
import { attrRules } from './attrRules.mjs';
import { AST_RULES, parseAst, astRules, quote, locate } from './astRules.mjs';

const Q = {
    indent: 'code layout strictly 2-indented',
    autoBound: 'before the `given` section, omit auto-bound implicits',
    order: 'before the `given` section, list in order: line(s) of standalone instances (instImplicit), line(s) of implicit binder(s) and their dependent instances (instImplicit) on the same line, line(s) of bare implicit binders',
    deflt: 'default arguments should be put within the `given` section',
    propFirst: 'within the `given` section: propositions come first, expressions come next, unless otherwise specified',
    combine: 'arguments of the same type should be combined, eg: {a b: Type} or (a b: Type)',
    imply: 'conclusion must be put within the `imply` section',
    proof: 'proof body must be put within the `proof` section',
    binop: 'within proof, binary operators `:` `+` `-` `*` `/` `=` `≠` `>` `<` `≥` `≤` should not be indented by new lines',
    bullet: 'After a bullet tactic (`·`), put the next statement on a new line when that branch contains more than one step.',
    swap: 'Use `obtain` instead of `rcases`, `if … then … else …` instead of `by_cases` (if it is not followed by `<;>`), `have` instead of `haveI`, and `let` instead of `letI`.',
    haveOnce: 'inline `have` without introducing `show` if it is referenced only once, e.g.: prefer `apply` instead of `exact`, perhaps by creating some holes.',
    calc: 'use `calc` instead of `by calc`, start `calc` with `_`',
    calcIn: 'avoid `calc` within [] block of `rw`/`erw`/`simp`, or within () as arguments',
    parenBy: 'no multi-line tactics inside parentheses, the tactic within compact type-ascribed `by` term (by tactic : Type) should be one-liner with no `;`',
    fromBy: 'follow `show` with `from`/`by` instead of `from by`',
    byExact: '`by exact expr` should be simplifed to `expr`',
    hole: 'use `_` as unused binders or unnamed holes, prefer `_` instead of `?_`/`?identifier`/`_identifier`',
    date: 'date created must be today, if date updated is the same as date created, it should be omitted.',
    openSec: 'use `open Section` if lemmas from that Section are imported',
    openDel: 'check delete_open.* to simplify `open` statements',
    openPrefix: 'after `open Section`, prefer the short lemma name when unambiguous',
    mp: 'For `LHS.is.RHS` tagged with `@[mp]` / `@[mpr]`, prefer the generated one-direction lemmas `RHS.of.LHS` / `LHS.of.RHS` over calling `.mp` / `.mpr` on the iff.',
    comm: 'For `LHS.eq.RHS` tagged with `@[comm]`, prefer the generated commutative lemma `RHS.eq.LHS` over `simp [← LHS.eq.RHS]` or `rw [LHS.eq.RHS.symm]`.',
    docstring: 'Run `python py/docstring.py <leanFile>` if necessary. It\'ll generate the attribute docstring table if the lemma uses attributes other than `@[main]`.',
};

/** rule id → AGENTS.md quote */
export const RULES = {
    'indent-odd': Q.indent,
    'indent-deep': Q.indent,
    'binder-auto-bound': Q.autoBound,
    'binder-order': Q.order,
    'binder-dep-inst': Q.order,
    'default-arg-given': Q.deflt,
    'given-prop-first': Q.propFirst,
    'binder-combine': Q.combine,
    'section-imply': Q.imply,
    'section-proof': Q.proof,
    'proof-binop-newline': Q.binop,
    'bullet-newline': Q.bullet,
    'tactic-rcases': Q.swap,
    'tactic-by-cases': Q.swap,
    'tactic-haveI': Q.swap,
    'tactic-letI': Q.swap,
    // not an AGENTS.md rule (user request): the warning text carries the reason
    'calc-after-assign': null,
    'have-inline-once': Q.haveOnce,
    'by-calc': Q.calc,
    'calc-start-underscore': Q.calc,
    'calc-in-brackets': Q.calcIn,
    'paren-by-multiline': Q.parenBy,
    'paren-by-semicolon': Q.parenBy,
    'from-by': Q.fromBy,
    'by-exact': Q.byExact,
    'hole-question': Q.hole,
    'binder-underscore-name': Q.hole,
    'date-created-missing': Q.date,
    'date-created-today': Q.date,
    'date-updated-same': Q.date,
    'date-order': Q.date,
    'open-section': Q.openSec,
    'open-unused': Q.openDel,
    'open-duplicate': Q.openDel,
    'open-prefix': Q.openPrefix,
    'attr-mp': Q.mp,
    'attr-comm': Q.comm,
    'attr-docstring': Q.docstring,
};

/** rules switched off by default (too noisy on the corpus; see the calibration notes in the README) */
export const DISABLED = new Set([
    'open-unused', // every corpus hit opens a section that is also a Mathlib / sympy namespace (e.g. `open MeasureTheory` for ∫, volume)
]);

const ymd = (d) => `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`;

/**
 * @param {string} source
 * @param {{
 *   file?: string,          // repo-relative path, used in messages (`Lemma/…/X.lean`)
 *   root?: string,          // repo root: enables `attr-mp` / `attr-comm` (reads the cited lemma files)
 *   sections?: Iterable<string>,
 *   today?: string,         // YYYY-MM-DD (default: local date)
 *   isNew?: boolean,        // file untracked / added in git (enables `date-created-today`)
 *   rules?: Iterable<string>, // only these rule ids
 *   ast?: boolean,          // false: skip the lean.js AST pass (text-scan fallbacks run instead)
 * }} [opts]
 */
export function lintLean(source, opts = {}) {
    const P = prepare(source);
    const warnings = [];
    const only = opts.rules ? new Set(opts.rules) : null;
    const ctx = {
        source: String(source ?? ''),
        P,
        file: opts.file,
        root: opts.root,
        today: opts.today ?? ymd(new Date()),
        isNew: !!opts.isNew,
        isLemmaFile: opts.file ? /(^|\/)Lemma\//.test(opts.file.replace(/\\/g, '/')) : true,
        sections: new Set(opts.sections ?? listLemmaTopLevelDirs()),
        decls: findDecls(P),
        astCovered: new Set(),
        astCursor: 0,
        /** AST rules: quote the statement (`stmt`), find its line in the source when possible */
        warnAst(rule, node, msg, maxLines = 2, follow = null) {
            const stmt = quote(node, 120, maxLines);
            // another node with the same text as the previous finding: it is further down
            const last = ctx.astLast;
            const from = last && last.node !== node && last.stmt === stmt && last.line != null ? last.line : ctx.astCursor;
            const line = locate(P.raw, stmt, from, follow ? quote(follow, 120, 1) : null);
            if (line != null) ctx.astCursor = line - 1;
            ctx.astLast = { node, stmt, line };
            ctx.warn(rule, line, null, msg, { stmt });
        },
        warn(rule, line, col, msg, extra = {}) {
            if (only ? !only.has(rule) : DISABLED.has(rule)) return;
            const quote = RULES[rule];
            warnings.push({
                type: 'warning',
                rule,
                line,
                ...(col != null ? { col } : {}),
                code: line != null ? P.raw[line - 1] ?? '' : extra.stmt ?? '',
                info: `[${rule}] ${msg}${quote ? ` (AGENTS.md: "${quote}")` : ''}`,
                ...extra,
            });
        },
    };
    ctx.scan = scanImportsAndOpens(P);
    // AST pass (lean.js); on a parse failure only the text rules run
    const tree = opts.ast === false ? null : parseAst(source);
    if (tree) for (const r of AST_RULES) ctx.astCovered.add(r);
    const steps = [openSection, openUnusedAndDuplicate, openPrefix, attrDocstring, dates, signatureRules, indentRules, proofRules, underscoreNameRule, attrRules];
    for (const step of steps) {
        try {
            step(ctx);
        } catch (e) {
            console.warn(`[lemmaLint] ${step.name}: ${e?.message || e}`);
        }
    }
    if (tree) {
        try {
            astRules(ctx, tree);
        } catch (e) {
            console.warn(`[lemmaLint] astRules: ${e?.message || e}`);
        }
    }
    warnings.sort((a, b) => (a.line ?? Infinity) - (b.line ?? Infinity) || (a.col ?? 0) - (b.col ?? 0));
    return warnings;
}

/**
 * Is `abs` new to git (untracked or staged as added)? Read-only `git status`; false when git is unavailable.
 * @param {string} abs absolute path of the file
 */
export function isNewInGit(abs) {
    try {
        const out = execFileSync('git', ['status', '--porcelain', '--untracked-files=all', '--', path.basename(abs)], {
            cwd: path.dirname(abs), encoding: 'utf8', timeout: 5000, stdio: ['ignore', 'pipe', 'ignore'],
        });
        return /^(\?\?|A)/m.test(out);
    } catch {
        return false;
    }
}

/**
 * Lint a file on disk the way the compiler does (repo root derived from the `Lemma/` component of the path).
 * @param {string} source
 * @param {string} leanAbsPath
 */
export function lintLeanFile(source, leanAbsPath, opts = {}) {
    const norm = String(leanAbsPath).replace(/\\/g, '/');
    const k = norm.lastIndexOf('/Lemma/');
    const root = k >= 0 ? norm.slice(0, k) : undefined;
    const file = k >= 0 ? norm.slice(k + 1) : path.basename(norm);
    return lintLean(source, { file, root, isNew: isNewInGit(leanAbsPath), ...opts });
}
