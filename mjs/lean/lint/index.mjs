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
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { listLemmaTopLevelDirs } from '../lemmaSections.mjs';
import { prepare, findDecls } from './scan.mjs';
import { scanImportsAndOpens, headerSpacing, maxHeartbeats, openSection, openDuplicate, openPrefix, attrDocstring, dates, declKeywordDirText, blankSublemmas } from './headerRules.mjs';
import { signatureRules } from './signatureRules.mjs';
import { indentRules, proofRules, underscoreNameRule } from './proofRules.mjs';
import { attrRules } from './attrRules.mjs';
import { AST_RULES, parseAst, astRules, quote, locate, countLemmaTheoremNodes } from './astRules.mjs';

const Q = {
    indent: 'code layout strictly 2-indented',
    autoBound: 'before the `given` section, omit auto-bound implicits',
    order: 'before the `given` section, list in order: line(s) of standalone instances (instImplicit), line(s) of implicit binder(s) and their dependent instances (instImplicit) on the same line, line(s) of bare implicit binders',
    deflt: 'default arguments should be put within the `given` section',
    explicitAbove: 'explicit binders `(…)` (hypotheses and given-section expressions) sit under `-- given`; type binders `{…}` / `⦃…⦄` and instance binders `[…]` stay above it',
    propFirst: 'within the `given` section: propositions come first, expressions come next, unless otherwise specified',
    givenInst: 'an instance binder that a later given hypothesis needs stays an instance binder `[instImplicit]` inside `-- given`, before that hypothesis; never `(h : … := by infer_instance)` or any `(h : T := by tactic)`',
    combine: 'arguments of the same type should be combined, eg: {a b: Type} or (a b: Type)',
    given: 'partition the lemma into `-- given`, `-- imply`, and `-- proof` (hypotheses under `given`, conclusion under `imply`, tactics under `proof`)',
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
    dateSp: 'exactly two blank lines before `-- created on`',
    openSec: 'use `open Section` if lemmas from that Section are imported',
    openDup: 'simplify `open` statements',
    openPrefix: 'after `open Section`, prefer the short lemma name when unambiguous',
    headerSp: '`import` / `open` / `set_option` are contiguous (no blank lines between them), then exactly two blank lines before the rest of the file',
    heartbeats: '`set_option maxHeartbeats` (and other elaborator heartbeat budgets) may be set or raised to any value strictly below 1000000. 1000000 and above stay disallowed.',
    mp: 'For `LHS.is.RHS` tagged with `@[mp]` / `@[mpr]`, prefer the generated one-direction lemmas `RHS.of.LHS` / `LHS.of.RHS` over calling `.mp` / `.mpr` on the iff.',
    comm: 'For `LHS.eq.RHS` tagged with `@[comm]`, prefer the generated commutative lemma `RHS.eq.LHS` over `simp [← LHS.eq.RHS]` or `rw [LHS.eq.RHS.symm]`.',
    declDir: 'Never put a `theorem` in `Lemma/`.', // removed from AGENTS.md: this warning checks it
    docstring: 'Run `python py/docstring.py <leanFile>` if necessary. It\'ll generate the attribute docstring table if the lemma uses attributes other than `@[path]`.',
};

/** rule id → AGENTS.md quote */
export const RULES = {
    'indent-odd': Q.indent,
    'indent-deep': Q.indent,
    'binder-auto-bound': Q.autoBound,
    'binder-order': Q.order,
    'binder-dep-inst': Q.order,
    'default-arg-given': Q.deflt,
    'explicit-above-given': Q.explicitAbove,
    'given-prop-first': Q.propFirst,
    // not an AGENTS.md rule: an explicit `-- given` binder that a later hypothesis mentions is an implicit above `-- given`
    'given-implicit-dep': null,
    'given-inst': Q.givenInst,
    // not an AGENTS.md rule (user request): the page typesets only the first run of `given` propositions
    'given-prop-consecutive': null,
    // not an AGENTS.md rule: numbered `h₀`/`h0`… in `-- given` must start at 0 with no gaps, and lower indices must appear earlier
    'given-hyp-index': null,
    // not an AGENTS.md rule: drop redundant `({…} : Set _)` on the LHS of ⊆/⊂/∈/… in `-- given`
    'redundant-set-ascription': null,
    'binder-combine': Q.combine,
    'section-given': Q.given,
    // not an AGENTS.md rule: a `-- given` with no binders under it should be deleted
    'section-given-empty': null,
    'section-imply': Q.imply,
    'section-proof': Q.proof,
    // not an AGENTS.md rule: no empty lines inside the proof body (enforced by the linter)
    'proof-blank-line': null,
    // not an AGENTS.md rule: exactly one blank line between consecutive private lemmas
    'blank-sublemmas': null,
    'proof-binop-newline': Q.binop,
    'bullet-newline': Q.bullet,
    'tactic-rcases': Q.swap,
    'tactic-by-cases': Q.swap,
    'tactic-haveI': Q.swap,
    'tactic-letI': Q.swap,
    // not an AGENTS.md rule (user request): the warning text carries the reason
    'calc-after-assign': null,
    // not an AGENTS.md rule (user request): `(x[t])` / `(x[t:])` -> drop the parens
    'paren-getelem': null,
    // not an AGENTS.md rule (user request): `f (x)` / `path (s)` -> drop the parens
    'paren-apparg': null,
    // not an AGENTS.md rule (user request): `(h : (T))` -> drop redundant parens around binder type
    'paren-redundant-type': null,
    // not an AGENTS.md rule (user request via Matrix/Body): `a - (∑ …)` -> drop parens around ∑/∏ RHS of `-`
    'paren-redundant-sum-sub': null,
    'have-inline-once': Q.haveOnce,
    'by-calc': Q.calc,
    'calc-start-underscore': Q.calc,
    // not an AGENTS.md rule: bare `calc`; every `_` step at calc+2 (enforced by the linter)
    'calc-underscore-align': null,
    // not an AGENTS.md rule: `_ =` not alone — RHS on same line (enforced by the linter)
    'calc-underscore-rhs': null,
    'calc-in-brackets': Q.calcIn,
    'paren-by-multiline': Q.parenBy,
    'paren-by-semicolon': Q.parenBy,
    'from-by': Q.fromBy,
    'by-exact': Q.byExact,
    // not an AGENTS.md rule (user request): a single-`exact` proof → term mode; the warning text carries the layout
    'term-mode-exact': null,
    // not AGENTS.md rules (user request): the warning text carries the reason
    'rw-exact': null,
    'show-multiline': null,
    'joint-random-symbol': null,
    'hole-question': Q.hole,
    'binder-underscore-name': Q.hole,
    'date-created-missing': Q.date,
    'date-created-today': Q.date,
    'date-updated-same': Q.date,
    'date-order': Q.date,
    'date-spacing': Q.dateSp,
    'open-section': Q.openSec,
    'open-duplicate': Q.openDup,
    'open-prefix': Q.openPrefix,
    'header-spacing': Q.headerSp,
    'max-heartbeats': Q.heartbeats,
    'attr-mp': Q.mp,
    'attr-comm': Q.comm,
    'attr-docstring': Q.docstring,
    'decl-keyword-dir': Q.declDir,
};

/** rules switched off by default (too noisy on the corpus; see the calibration notes in the README) */
export const DISABLED = new Set([
]);

const ymd = (d) => `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`;

/**
 * @param {string} source
 * @param {{
 *   file?: string,          // repo-relative path, used in messages (`Lemma/…/X.lean`)
 *   root?: string,          // repo root: enables `attr-mp` / `attr-comm` (reads the cited lemma files)
 *   sections?: Iterable<string>,
 *   today?: string,         // YYYY-MM-DD (default: local date)
 *   isNew?: boolean,        // truly new in git (`??`/`A` with no matching delete/rename; enables `date-created-today`)
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
    // `decl-keyword-dir`: trust the tree only when it sees the same lemma/theorem declarations as the text scan
    if (tree && countLemmaTheoremNodes(tree) !== ctx.decls.filter((d) => d.kind === 'lemma' || d.kind === 'theorem').length)
        ctx.astCovered.delete('decl-keyword-dir');
    const steps = [headerSpacing, maxHeartbeats, openSection, openDuplicate, openPrefix, declKeywordDirText, attrDocstring, dates, blankSublemmas, signatureRules, indentRules, proofRules, underscoreNameRule, attrRules];
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
    // `term-mode-exact` takes precedence inside a single-`exact` proof: the hints to write `apply` (with holes) instead of
    // `exact` (`have-inline-once`, `hole-question` in an `exact`) and a `by-exact` at the same `by` are dropped there
    const tm = ctx.termModeExact ?? [];
    const superseded = (w) => w.line != null && tm.some((r) => w.line - 1 >= r.from && w.line - 1 <= r.to && (
        w.rule === 'have-inline-once' ||
        (w.rule === 'hole-question' && /^exact/.test(w.hole ?? '')) ||
        (w.rule === 'by-exact' && w.line - 1 === r.byLine && w.col === r.byCol + 1)));
    if (tm.length) warnings.splice(0, warnings.length, ...warnings.filter((w) => !superseded(w)));
    warnings.sort((a, b) => (a.line ?? Infinity) - (b.line ?? Infinity) || (a.col ?? 0) - (b.col ?? 0));
    return warnings;
}

const GIT_OPTS = { encoding: 'utf8', timeout: 5000, stdio: ['ignore', 'pipe', 'ignore'] };

function gitOut(cwd, args) {
    return execFileSync('git', args, { cwd, ...GIT_OPTS });
}

/** Resolve symlinks so `/home/…/src/lean` and `/home/…/github/lean` share one relative path. */
function realpath(p) {
    try {
        return fs.realpathSync(p);
    } catch {
        return path.resolve(p);
    }
}

function repoRel(gitRoot, abs) {
    return path.relative(realpath(gitRoot), realpath(abs)).split(path.sep).join('/');
}

function createdOnDate(src) {
    const m = /(?:^|\n)\s*--\s*created on\s+(\d{4}-\d{2}-\d{2})\s*(?:\n|$)/.exec(src);
    return m ? m[1] : null;
}

function lineOverlap(a, b) {
    const lines = (s) => new Set(s.split('\n').map((l) => l.trim()).filter(Boolean));
    const sa = lines(a);
    const sb = lines(b);
    if (!sa.size && !sb.size) return 1;
    let n = 0;
    for (const x of sa) if (sb.has(x)) n++;
    return n / Math.max(sa.size, sb.size);
}

function porcelainPath(line) {
    if (!line || line.length < 4) return '';
    let rest = line.slice(3);
    const xy = line.slice(0, 2);
    if (xy[0] === 'R' || xy[0] === 'C') {
        const i = rest.indexOf(' -> ');
        if (i >= 0) rest = rest.slice(i + 4);
    }
    return rest.replace(/^"(.*)"$/, '$1').replace(/\\/g, '/');
}

function isAddedOrUntracked(line) {
    return line.startsWith('??') || line[0] === 'A' || line[1] === 'A';
}

function isLemmaLean(p) {
    return p.startsWith('Lemma/') && p.endsWith('.lean') && !p.endsWith('.echo.lean');
}

function deletedLemmaPaths(gitRoot) {
    const parts = [
        gitOut(gitRoot, ['ls-files', '-z', '--deleted', '--', 'Lemma']),
        gitOut(gitRoot, ['diff', '-z', '--name-only', '--diff-filter=D', '--cached', '--', 'Lemma']),
    ].join('\0');
    return [...new Set(parts.split('\0').filter(isLemmaLean))];
}

/** `Lemma/Foo/Bar/Baz.lean` → `Foo.Bar.Baz` (rename.sh module form). */
function lemmaPathToModule(rel) {
    return String(rel)
        .replace(/\\/g, '/')
        .replace(/^Lemma\//, '')
        .replace(/\.lean$/, '')
        .split('/')
        .filter(Boolean)
        .join('.');
}

/**
 * `sh/rename.sh` often shortens/lengthens the module path while also editing the body
 * (e.g. CountableMeasure rewrite). Same created date + module prefix is enough then:
 * `Measure.Measure.eq.Count.of.…` ↔ `Measure.Measure.eq.Count`.
 */
function relatedLemmaModules(a, b) {
    if (!a || !b) return false;
    return a === b || a.startsWith(b + '.') || b.startsWith(a + '.');
}

/**
 * Radical `lemmaPath` renames (e.g. `Eq.ArgMax.Mul.…` → `GetArgMaxProbCond.eq.ArgMax.…`) share
 * tokens even when neither module is a prefix of the other.
 */
function moduleTokenOverlap(a, b) {
    const toks = (m) => new Set(String(m).split('.').filter((t) => t.length >= 3));
    const sa = toks(a);
    const sb = toks(b);
    if (!sa.size || !sb.size) return 0;
    let n = 0;
    for (const t of sa) if (sb.has(t)) n++;
    return n / Math.max(sa.size, sb.size);
}

/**
 * `mv` / `rename.sh`: deleted old lemma + untracked/added dest with the same blob, same created
 * date + body overlap, same created date + related module path, same created date + shared module
 * tokens, or a **unique** deleted lemma with the same `-- created on` (covers radical renames when
 * HEAD still has a tiny axiom stub so line overlap is low).
 */
function isMoveOfExistingLemma(gitRoot, abs) {
    const now = fs.readFileSync(abs, 'utf8');
    const nowCreated = createdOnDate(now);
    const nowMod = lemmaPathToModule(repoRel(gitRoot, abs));
    let nowHash = null;
    try {
        nowHash = gitOut(gitRoot, ['hash-object', abs]).trim();
    } catch { /* ignore */ }
    const sameDateOlds = [];
    for (const old of deletedLemmaPaths(gitRoot)) {
        try {
            if (nowHash && gitOut(gitRoot, ['rev-parse', `HEAD:${old}`]).trim() === nowHash) return true;
            const oldSrc = gitOut(gitRoot, ['show', `HEAD:${old}`]);
            if (!(nowCreated && nowCreated === createdOnDate(oldSrc))) continue;
            sameDateOlds.push(old);
            if (lineOverlap(now, oldSrc) >= 0.7) return true;
            const oldMod = lemmaPathToModule(old);
            if (relatedLemmaModules(nowMod, oldMod)) return true;
            if (moduleTokenOverlap(nowMod, oldMod) >= 0.25) return true;
        } catch {
            continue;
        }
    }
    // Unique `-- created on` among deletions ⇒ rename kept its birth date (do not demand today).
    if (sameDateOlds.length === 1) return true;
    return false;
}

/**
 * Is `abs` a truly new git file (untracked or staged as added), not a path move of an existing lemma?
 * Read-only `git status`; false when git is unavailable. Uses the repo-relative path (not the basename).
 * @param {string} abs absolute path of the file
 */
export function isNewInGit(abs) {
    try {
        const gitRoot = realpath(gitOut(path.dirname(abs), ['rev-parse', '--show-toplevel']).trim());
        const rel = repoRel(gitRoot, abs);
        if (rel.startsWith('..')) return false;
        const out = gitOut(gitRoot, ['status', '--porcelain', '--untracked-files=all', '--', rel]);
        const hit = out.split('\n').filter(Boolean).find((l) => porcelainPath(l) === rel);
        if (!hit || !isAddedOrUntracked(hit)) return false;
        if (isMoveOfExistingLemma(gitRoot, abs)) return false;
        return true;
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
