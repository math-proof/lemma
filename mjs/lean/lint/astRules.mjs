/**
 * AST-based lint rules on the lean.js parse tree (`js/parser/lean.js`).
 *
 * The tree stamps a 1-based `line` on every node (`js/parser/lean.js`) but has no columns, so these warnings
 * quote the offending statement (`String(node)`, the tree's own reprint) in `stmt` and report `node.line`.
 * A text search (`locate`) remains only as a fallback for synthetic quotes / `paren-redundant-arith`.
 * A parse failure disables the AST rules silently and the text-scan fallbacks run instead (see `AST_RULES`).
 */
import '../../../js/py.js';
import { compile, Lean, LeanModule } from '../../../js/parser/lean.js';

/** rule ids implemented here; their text-scan versions only run when the AST is unavailable */
export const AST_RULES = new Set(['have-inline-once', 'have-underscore', 'given-prop-first', 'given-prop-consecutive', 'given-implicit-dep', 'tactic-haveI', 'tactic-letI', 'calc-after-assign', 'decl-keyword-dir', 'public-section', 'paren-getelem', 'fin-index-val', 'fin-getelem-app', 'paren-apparg', 'paren-redundant-type', 'paren-redundant-sum-sub', 'paren-redundant-pow', 'paren-redundant-binder', 'paren-redundant-arith', 'paren-redundant-ascription', 'prefer-unicode-type', 'prefer-unicode-pow', 'range-binder', 'literal-left-comparison', 'dot-notation']);

/**
 * Term forms whose parentheses are load-bearing inside an ascription: `(fun y => F y : T)`
 * rebinds the colon into the lambda, `(a, b : α × β)` is no longer a tuple, and so on.
 * Even when the reprint happens to re-parse the same way, these stay parenthesized.
 */
const ASCRIPTION_KEEP_PARENS = new Set([
    'Lean_fun', 'LeanIte', 'LeanBy', 'LeanBrace', 'LeanAngleBracket', 'LeanColon',
    'LeanArgsCommaSeparated', 'Lean_match', 'Lean_let', 'Lean_do', 'Lean_calc',
    'Lean_have', 'Lean_suffices', 'Lean_show', 'LeanLambda',
]);

/** Parse one term in isolation (as a `have` value) and return the term node, or null. */
function parseTermNode(text) {
    try {
        const tree = compile(`private lemma __lint__ : True := by\n  have __h__ := ${text}\n  trivial\n`);
        for (const n of walk(tree)) {
            if (n?.constructor?.name === 'Lean_have') return n.args?.[0]?.rhs ?? null;
        }
    } catch {
        // unparseable wrapper: no suggestion
    }
    return null;
}

/** parse `source`, or null when the parser throws / does not return a module */
export function parseAst(source) {
    try {
        const tree = compile(source.replace(/\r/g, '')); // the parser warns on every CR
        return tree instanceof LeanModule ? tree : null;
    } catch {
        return null;
    }
}

const collapse = (s) => s.replace(/\s+/g, '');

/** the statement as printed by the tree, trimmed to its first lines / ~120 chars */
export function quote(node, maxLen = 120, maxLines = 2) {
    let s = String(node).replace(/^\n+/, '').replace(/\s+$/, '');
    const lines = s.split('\n');
    const ind = Math.min(...lines.filter((l) => l.trim()).map((l) => l.length - l.trimStart().length));
    s = lines.map((l) => l.slice(ind)).slice(0, maxLines).join('\n');
    const cut = lines.length > maxLines;
    if (s.length > maxLen) return `${s.slice(0, maxLen)}…`;
    return cut ? `${s} …` : s;
}

function* walk(node) {
    if (!node || typeof node !== 'object') return;
    yield node;
    if (Array.isArray(node.args)) for (const c of node.args) yield* walk(c);
}

function tokens(node, name) {
    const { LeanToken } = Lean.classes;
    let n = 0;
    for (const x of walk(node)) if (x instanceof LeanToken && x.text === name) n++;
    return n;
}

const isTrivia = (n) => {
    const { LeanCaret, LeanLineComment } = Lean.classes;
    return n instanceof LeanCaret || n instanceof LeanLineComment;
};

// ---------------------------------------------------------------------------------------------------------------

/**
 * `have h … := …` whose name is used exactly once, by the very next statement, an `exact` / `apply`
 * (not `… at h`): inline it, e.g. `apply` with a hole and prove it afterwards.
 */
function haveInlineOnce(ctx, stmts) {
    const { Lean_have, Lean_replace, LeanAssign, LeanColon, LeanToken, LeanTactic, LeanAt, Lean_let, Lean_set, Lean_fun } = Lean.classes;
    const args = stmts.args;
    for (let i = 0; i < args.length; i++) {
        const st = args[i];
        if (!(st instanceof Lean_have) || st instanceof Lean_replace || st.args.length !== 1) continue;
        const assign = st.args[0];
        if (!(assign instanceof LeanAssign)) continue;
        let lhs = assign.lhs;
        // typed `have h : T :=` whose type includes `fun`: the ascription may be
        // required for elaboration (`Measurable.of_eval` / `.comp` needs
        // `Measurable fun residual : (ℕ → ℝ) => ...`). Inlining would drop it
        // (Random / importance_sampling `hinner`).
        if (lhs instanceof LeanColon) {
            const typ = lhs.rhs;
            if (Lean_fun && typ && [...walk(typ)].some((x) => x instanceof Lean_fun)) continue;
            lhs = lhs.lhs;
        }
        if (!(lhs instanceof LeanToken) || !lhs.text || lhs.text === 'this' || lhs.text === '_') continue;
        const name = lhs.text;
        let j = i + 1;
        while (j < args.length && isTrivia(args[j])) j++;
        const next = args[j];
        if (!(next instanceof LeanTactic) || !['exact', 'apply'].includes(next.tacticName)) continue;
        if ([...walk(next)].some((x) => x instanceof LeanAt)) continue;
        if (tokens(next, name) !== 1) continue;
        // no other use in the rest of the block (until the name is bound again)
        let others = 0;
        for (let k = j + 1; k < args.length; k++) {
            const s = args[k];
            if ((s instanceof Lean_let || s instanceof Lean_set) && s.args[0] instanceof LeanAssign) {
                let l = s.args[0].lhs;
                if (l instanceof LeanColon) l = l.lhs;
                if (l instanceof LeanToken && l.text === name) break;
            }
            others += tokens(s, name);
        }
        if (others) continue;
        ctx.warnAst('have-inline-once', st,
            `\`${name}\` is used only once, by the next \`${next.tacticName}\`: inline it (e.g. \`apply\` with a hole \`_\` and prove it afterwards) instead of a \`have\``,
            2, next);
    }
}

// ---------------------------------------------------------------------------------------------------------------

/**
 * `have _ := ...` / `have _ : T := ...`: the underscore binder discards the result, so the `have` is redundant —
 * inline the RHS or drop the statement. Named `have h :=`, anonymous `have : T :=` (binds `this`), pattern
 * binders (`have ⟨_, h⟩ :=`), and `haveI` (see `tactic-haveI`) are out of scope. Not `let _ :=`.
 */
function haveUnderscore(ctx, node) {
    const { Lean_have, Lean_replace, LeanAssign, LeanColon, LeanToken } = Lean.classes;
    if (!(node instanceof Lean_have) || node instanceof Lean_replace || node.inst) return;
    if (node.args.length !== 1) return;
    const assign = node.args[0];
    if (!(assign instanceof LeanAssign)) return;
    let lhs = assign.lhs;
    if (lhs instanceof LeanColon) lhs = lhs.lhs;
    if (!(lhs instanceof LeanToken) || lhs.text !== '_') return;
    ctx.warnAst('have-underscore', node,
        '`have _ :=` is redundant: the underscore discards the result — inline or drop the `have`',
        1);
}

// ---------------------------------------------------------------------------------------------------------------

const PREDICATE_HEAD = /^(Is[A-Z]|Has[A-Z]|Odd$|Even$|Prime$|Nat\.Prime$|Squarefree$|Irreducible$|Continuous|Differentiable|Monotone|Antitone|StrictMono|StrictAnti|Injective$|Surjective$|Bijective$|Function\.|Measurable|AEMeasurable|Integrable|Summable|HasSum|Tendsto$|Filter\.Tendsto$|Nonempty$|Set\.Nonempty$|Finite$|Infinite$|Countable$|Bounded|BddAbove$|BddBelow$|Coprime$|Nat\.Coprime$|Disjoint$|Pairwise$|Antisymm|Symmetric$|Transitive$|Reflexive$|Convex|Concave|Fact$|Decidable$|Subsingleton$|Unique$)/;

const TYPE_HEAD = /^(Decidable|DecidablePred|DecidableEq|DecidableRel|Fintype|Finite|Inhabited|Nonempty|Set|Finset|List|Multiset|Matrix|Tensor|Fin|Option|Vector|Type\*?|Sort\*?)$/;

/** 'prop' | 'expr' | null for an explicit binder `(names : type)` */
function binderKind(names, type) {
    const { LeanBinaryBoolean, LeanQuantifier, LeanNot, Lean_lnot, LeanToken, LeanArgsSpaceSeparated, LeanRightarrow, Lean_rightarrow, LeanProperty } = Lean.classes;
    const hyp = names.length > 0 && names.every((n) => /^_?h/.test(n));
    const isProp = (t) => t instanceof LeanBinaryBoolean || t instanceof LeanQuantifier || t instanceof LeanNot || t instanceof Lean_lnot
        || ((t instanceof Lean_rightarrow || t instanceof LeanRightarrow) && isProp(t.rhs))
        || (t instanceof LeanToken && /^(True|False)$/.test(t.text));
    if (isProp(type)) return 'prop';
    // a type-valued binder (`Decidable p`, `(x : α) → Fintype …`) is never a proposition, whatever its name
    let last = type;
    while (last instanceof Lean_rightarrow || last instanceof LeanRightarrow) last = last.rhs;
    const lastHead = String(last instanceof LeanArgsSpaceSeparated ? last.args[0] : last).trim();
    if (TYPE_HEAD.test(lastHead)) return hyp ? null : 'expr';
    if (hyp) return 'prop';
    if (type instanceof LeanToken) return type.text === 'Prop' ? null : 'expr';
    if (type instanceof Lean_rightarrow || type instanceof LeanRightarrow) return 'expr';
    if (type instanceof LeanArgsSpaceSeparated || type instanceof LeanProperty) {
        const head = String(type instanceof LeanArgsSpaceSeparated ? type.args[0] : type).trim();
        return PREDICATE_HEAD.test(head) ? null : 'expr';
    }
    return null;
}

/** `name binders…` (the `LeanArgsIndented` before the declaration's `:`), or null */
function signature(decl) {
    const { LeanAssign, LeanColon, LeanArgsIndented } = Lean.classes;
    let sig = decl.args.find((a) => a instanceof LeanAssign)?.lhs;
    while (sig instanceof LeanAssign) sig = sig.lhs; // `lemma … : T := … := by` nests assigns
    if (sig instanceof LeanColon) sig = sig.lhs;
    return sig instanceof LeanArgsIndented ? sig : null;
}

/** declaration name (first token of the signature), or null */
function declName(decl) {
    const { LeanToken } = Lean.classes;
    const name = signature(decl)?.args[0];
    return name instanceof LeanToken ? name.text : null;
}

/** inside a declaration's signature (binders / conclusion) rather than its proof */
function inSignature(node) {
    const { LeanAssign, Lean_lemma, Lean_theorem, Lean_def } = Lean.classes;
    for (let p = node; p?.parent; p = p.parent) {
        const a = p.parent;
        if (a instanceof LeanAssign && a.lhs === p && (a.parent instanceof Lean_lemma || a.parent instanceof Lean_theorem || a.parent instanceof Lean_def || a.parent instanceof LeanAssign)) {
            let d = a;
            while (d instanceof LeanAssign) d = d.parent;
            if (d instanceof Lean_lemma || d instanceof Lean_theorem || d instanceof Lean_def) return true;
        }
    }
    return false;
}

/** explicit binders of the `-- given` section of a lemma: [{ node, names, type, kind }] */
function givenBinders(decl) {
    const { LeanAssign, LeanColon, LeanArgsIndented, LeanArgsNewLineSeparated, LeanArgsSpaceSeparated, LeanParenthesis, LeanLineComment, LeanToken } = Lean.classes;
    const sig = signature(decl);
    if (!sig) return null;
    const lines = sig.args.find((a) => a instanceof LeanArgsNewLineSeparated);
    if (!lines) return null;
    const k = lines.args.findIndex((a) => a instanceof LeanLineComment && a.text.trim() === 'given');
    if (k < 0) return null;
    const out = [];
    for (const item of lines.args.slice(k + 1)) {
        if (item instanceof LeanLineComment) break; // another section marker
        const groups = item instanceof LeanArgsSpaceSeparated ? item.args : [item];
        for (const g of groups) {
            if (!(g instanceof LeanParenthesis) || !(g.arg instanceof LeanColon)) { out.push({ node: g, names: [], type: null, kind: null }); continue; }
            const c = g.arg;
            const nameNodes = c.lhs instanceof LeanArgsSpaceSeparated ? c.lhs.args : [c.lhs];
            if (!nameNodes.every((n) => n instanceof LeanToken)) { out.push({ node: g, names: [], type: null, kind: null }); continue; }
            const names = nameNodes.map((n) => n.text);
            out.push({ node: g, names, type: c.rhs, kind: binderKind(names, c.rhs) });
        }
    }
    return out;
}

/** names bound by the binder part of a quantifier / big operator / `fun`, and its parts evaluated outside the scope */
function binderParts(b) {
    const { LeanToken, LeanColon, LeanArgsSpaceSeparated, LeanParenthesis, LeanBrace } = Lean.classes;
    const names = [];
    const outside = [];
    const visit = (x) => {
        if (x instanceof LeanToken) names.push(x.text);
        else if (x instanceof LeanArgsSpaceSeparated) x.args.forEach(visit);
        else if (x instanceof LeanParenthesis || x instanceof LeanBrace) visit(x.arg);
        else if (x instanceof LeanColon || (x && x.lhs != null && x.rhs != null)) { visit(x.lhs); outside.push(x.rhs); } // `i : Fin n`, `k ∈ s`, `x > 0`
        else if (x) outside.push(x);
    };
    visit(b);
    return { names, outside };
}

/** does `node` mention `name` free (not re-bound by `∀ name, …` / `∑ name ∈ s, …` / `fun name => …` / a match-lambda arm)? */
function mentions(node, name) {
    const { LeanToken, LeanBigOperator, Lean_fun, LeanRightarrow, Lean_mapsto } = Lean.classes;
    if (!node || typeof node !== 'object') return false;
    if (node instanceof LeanToken) return node.text === name;
    // `fun | p => e | q => e`: each arm binds its own pattern, and a name bound by one arm is not bound in another.
    // Must run before any `node.arg instanceof …` check: on a match lambda `.arg` is a `LeanBar`.
    if (node instanceof Lean_fun && node.is_match_lambda) {
        return node.args.some((bar) => {
            const arrow = bar?.arg;
            if (!arrow || arrow.lhs == null || arrow.rhs == null) return mentions(bar, name);
            const { names, outside } = binderParts(arrow.lhs);
            if (outside.some((o) => mentions(o, name))) return true;
            return names.includes(name) ? false : mentions(arrow.rhs, name);
        });
    }
    let scope = null;
    if (node instanceof LeanBigOperator && node.args?.length === 2) scope = [node.args[0], node.args[1]];
    else if (node instanceof Lean_fun && (node.arg instanceof LeanRightarrow || node.arg instanceof Lean_mapsto)) scope = [node.arg.lhs, node.arg.rhs];
    if (scope) {
        const { names, outside } = binderParts(scope[0]);
        if (outside.some((o) => mentions(o, name))) return true;
        return names.includes(name) ? false : mentions(scope[1], name);
    }
    return Array.isArray(node.args) && node.args.some((c) => mentions(c, name));
}

/**
 * Names of the `given` expressions the propositions need: an expression whose name a proposition's type mentions,
 * closed over the types of those expressions (`(n : ℕ) (i : Fin n) (h : i < 3)` needs `i` and `n`).
 * Free occurrences only (`mentions`): a name re-bound inside a proposition (`∀ x, …`, `fun θ => …`) does not count.
 */
function neededExprs(bs) {
    const exprs = bs.filter((b) => b.kind === 'expr');
    const need = new Set();
    let grow = bs.filter((b) => b.kind === 'prop').map((b) => b.type);
    while (grow.length) {
        const next = [];
        for (const t of grow) {
            for (const e of exprs) {
                if (e.names.every((n) => need.has(n)) || !e.names.some((n) => mentions(t, n))) continue;
                for (const n of e.names) need.add(n);
                next.push(e.type);
            }
        }
        grow = next;
    }
    return need;
}

/**
 * In `-- given`, propositions come first: an expression binder followed by an independent proposition binder.
 * An expression some proposition needs (`neededExprs`) must stay above the propositions — moving a proposition
 * above it would split the proposition run (`given-prop-consecutive`), so it is not reported here.
 * Returns true when it warned.
 */
function givenPropFirst(ctx, decl, bs = givenBinders(decl)) {
    if (!bs) return false;
    const need = neededExprs(bs);
    for (let a = 0; a < bs.length; a++) {
        if (bs[a].kind !== 'expr' || bs[a].names.some((n) => need.has(n))) continue;
        // a proposition can move above `bs[a]` only if it mentions no name bound from `bs[a]` up to itself
        let bound = [];
        let prop = null;
        for (let b = a; b < bs.length; b++) {
            const x = bs[b];
            if (b > a && x.kind === 'prop' && !bound.some((n) => mentions(x.type, n))) { prop = x; break; }
            bound = bound.concat(x.names);
        }
        if (!prop) continue;
        ctx.warnAst('given-prop-first', prop.node,
            `proposition \`${quote(prop.node, 60, 1)}\` comes after the expression \`${quote(bs[a].node, 60, 1)}\` and does not depend on it: in \`given\`, propositions come first`);
        return true;
    }
    return false;
}

/**
 * An explicit binder under `-- given` whose names occur free in a *later binder of any kind*
 * (proposition, expression, instance, …) is not a given: it should be `{names : type}` above
 * `-- given`. Propositions stay. A name rebound by `∀` / `∃` / `∑` / `∏` / `fun` inside the later
 * binder's type does not count (`mentions`). A later proposition uses the "referenced by" wording;
 * a non-propositional dependent binder uses "determined by `(i : Fin (d + d))`" (the whole binder).
 * Returns true when it warned.
 */
function givenImplicitDep(ctx, decl, bs = givenBinders(decl)) {
    if (!bs) return false;
    let warned = false;
    for (let a = 0; a < bs.length; a++) {
        const b = bs[a];
        if (b.kind === 'prop' || !b.names.length || !b.type) continue;
        if (b.kind == null && b.names.every((n) => /^_?h/.test(n))) continue;
        if (String(b.node).includes(':=')) continue;
        // any later binder whose type mentions `n` determines `n` (proposition or not); `mentions`
        // ignores names rebound by ∀/∃/∑/∏/fun inside that type.
        const hits = b.names.map((n) => {
            const hyps = bs.slice(a + 1).filter((p) => p.type && mentions(p.type, n));
            const prop = hyps.filter((p) => p.kind === 'prop');
            const dep = hyps.filter((p) => p.kind !== 'prop');
            return { n, hyps, prop, dep };
        });
        const referenced = hits.filter((h) => h.hyps.length);
        if (!referenced.length) continue;
        const shown = quote(b.node, 80, 1);
        const imp = shown.startsWith('(') && shown.endsWith(')') ? `{${shown.slice(1, -1)}}` : `{${b.names.join(' ')} : …}`;
        // a non-propositional dependent binder determines the name; show the whole binder, not just its name.
        const hasDep = referenced.some((h) => h.dep.length);
        const desc = (h) => {
            const parts = [];
            if (h.dep.length) parts.push(`determined by ${h.dep.map((p) => `\`${quote(p.node, 80, 1)}\``).join(', ')}`);
            const propNames = [...new Set(h.prop.flatMap((p) => p.names))];
            if (propNames.length) parts.push(`referenced by ${propNames.map((n) => `\`${n}\``).join(', ')}`);
            return parts.join(' and ');
        };
        if (referenced.length === b.names.length) {
            const subject = hasDep ? referenced.map((h) => `\`${h.n}\``).join(', ') : `\`${shown}\``;
            ctx.warnAst('given-implicit-dep', b.node,
                `${subject} is ${referenced.map(desc).join('; ')}; it is not a given — change it to \`${imp}\` above \`-- given\``);
        } else {
            for (const h of referenced) {
                const subject = hasDep ? `\`${h.n}\`` : `\`${h.n}\` in \`${shown}\``;
                ctx.warnAst('given-implicit-dep', b.node,
                    `${subject} is ${desc(h)}; it is not a given — change \`${h.n}\` to \`{${h.n} : …}\` above \`-- given\``);
            }
        }
        warned = true;
    }
    return warned;
}

/**
 * `given-prop-consecutive`: the propositions of `-- given` must form one consecutive run. The page
 * (`render2vue` → `vue/lemma.vue`) shows `given` as: `explicit` (binders before the first
 * proposition, raw Lean) → `given` (the first run of propositions, one LaTeX block each) → `default` (everything
 * from the first expression after that run, raw Lean) — so a proposition after the gap is never typeset.
 * Canonical order: the expressions the propositions need, then all propositions, then the other expressions.
 */
function givenPropConsecutive(ctx, decl, bs = givenBinders(decl)) {
    if (!bs) return false;
    const typed = bs.filter((b) => b.kind === 'prop' || b.kind === 'expr');
    const p0 = typed.findIndex((b) => b.kind === 'prop');
    if (p0 < 0) return false;
    const g0 = typed.findIndex((b, i) => i > p0 && b.kind === 'expr');
    if (g0 < 0) return false;
    const late = typed.findIndex((b, i) => i > g0 && b.kind === 'prop');
    if (late < 0) return false;
    const prop = typed[late];
    const gap = typed.slice(g0, late).filter((b) => b.kind === 'expr');
    const props = typed.filter((b) => b.kind === 'prop');
    const need = neededExprs(bs);
    const exprs = typed.filter((b) => b.kind === 'expr');
    const before = exprs.filter((b) => b.names.some((n) => need.has(n)));
    const after = exprs.filter((b) => !b.names.some((n) => need.has(n)));
    const deps = gap.flatMap((b) => b.names).filter((n) => mentions(prop.type, n));
    const names = (xs) => xs.flatMap((b) => b.names).join(' ');
    const first = quote(typed[p0].node, 40, 1);
    let fix;
    if (gap.some((b) => b.names.some((n) => need.has(n)))) {
        // the gap holds expressions the propositions need: they go above the first proposition
        const move = before.filter((b) => typed.indexOf(b) > p0);
        // an expression typed by a proposition (`(x : Fin n)` after `(h : 0 < n)` is fine; `(y : {z // h z})` is not) cannot move
        if (move.some((b) => props.some((q) => q.names.some((n) => mentions(b.type, n))))) return false;
        const order = [before, props, after].filter((xs) => xs.length).map((xs) => `\`${names(xs)}\``).join(', then ');
        fix = (deps.length ? `it mentions ${deps.map((n) => `\`${n}\``).join(', ')}, so it cannot move above them; ` : '')
            + `move ${move.map((b) => `\`${quote(b.node, 40, 1)}\``).join(' ')} before \`${first}\` (order: ${order})`;
    } else {
        fix = `move it up to the propositions above (it does not depend on ${gap.map((b) => `\`${quote(b.node, 40, 1)}\``).join(' ')})`;
    }
    ctx.warnAst('given-prop-consecutive', prop.node,
        `proposition \`${quote(prop.node, 60, 1)}\` is separated from the propositions above by ${gap.map((b) => `\`${quote(b.node, 40, 1)}\``).join(' ')}: in \`given\`, keep all propositions consecutive (only the first run is typeset); ${fix}`);
    return true;
}

// ---------------------------------------------------------------------------------------------------------------

/** `haveI` / `letI` (the parser flags them with `inst`): use `have` / `let` */
function instanceVariant(ctx, node) {
    const { Lean_have } = Lean.classes;
    if (!node.inst || inSignature(node)) return; // in a statement, `letI` / `haveI` may be needed for instances
    const [rule, kw, plain] = node instanceof Lean_have ? ['tactic-haveI', 'haveI', 'have'] : ['tactic-letI', 'letI', 'let'];
    ctx.warnAst(rule, node, `use \`${plain}\` instead of \`${kw}\``, 1);
}

/**
 * `have h : T :=⏎ calc …`: the tree keeps the line break as a `LeanArgsNewLineSeparated` wrapping the `calc`
 * (the same-line form `:= calc` has the `LeanCalc` itself as the right-hand side).
 */
function calcAfterAssign(ctx, node) {
    const { LeanAssign, LeanArgsNewLineSeparated, LeanCalc } = Lean.classes;
    const assign = node.args[0];
    if (!(assign instanceof LeanAssign)) return;
    const rhs = assign.rhs;
    if (!(rhs instanceof LeanArgsNewLineSeparated) || rhs.args.length !== 1 || !(rhs.args[0] instanceof LeanCalc)) return;
    ctx.warnAst('calc-after-assign', node, `put \`calc\` on the same line right after \`:=\` (\`${node.keyword} … := calc\`), not on the next line`, 1);
}


/**
 * `y[i.val]` / `y[↑i]` / slice bounds: prefer bare Fin index `y[i]` (not `.val` or `↑`).
 * Only the index atom (or each comma-separated / colon bound) is checked; deeper `.val` / `↑`
 * inside arithmetic (`y[i.val + 1]`, `y[↑i + 1]`) is out of scope. Not an AGENTS.md rule
 * (user request via Random).
 */
function unwrapParens(node) {
    const { LeanParenthesis } = Lean.classes;
    let n = node;
    while (n instanceof LeanParenthesis) n = n.arg;
    return n;
}

function isValProjection(node) {
    const { LeanProperty, LeanToken } = Lean.classes;
    const n = unwrapParens(node);
    return n instanceof LeanProperty && n.rhs instanceof LeanToken && n.rhs.text === 'val' ? n : null;
}

/** `↑i` / `↑(…)` as a GetElem index atom (`Lean_uparrow`). */
function isUpArrowIndex(node) {
    const { Lean_uparrow } = Lean.classes;
    const n = unwrapParens(node);
    return n instanceof Lean_uparrow ? n : null;
}

/** Top-level index atoms of a GetElem index: comma parts, slice bounds; skip `; μ` measure tail. */
function* getElemIndexAtoms(idx) {
    const { LeanArgsCommaSeparated, LeanArgsSemicolonSeparated, LeanColon, LeanCaret } = Lean.classes;
    if (!idx) return;
    if (idx instanceof LeanArgsSemicolonSeparated) {
        yield* getElemIndexAtoms(idx.args[0]);
        return;
    }
    if (idx instanceof LeanArgsCommaSeparated) {
        for (const a of idx.args) yield* getElemIndexAtoms(a);
        return;
    }
    if (idx instanceof LeanColon) {
        if (idx.lhs && !(idx.lhs instanceof LeanCaret)) yield idx.lhs;
        if (idx.rhs && !(idx.rhs instanceof LeanCaret)) yield idx.rhs;
        return;
    }
    yield idx;
}

function finIndexVal(ctx, node) {
    const { LeanGet } = Lean.classes;
    if (!(node instanceof LeanGet)) return;
    const hits = [];
    for (const atom of getElemIndexAtoms(node.args[1])) {
        const prop = isValProjection(atom);
        if (prop) {
            const bad = String(prop).replace(/^\s+|\s+$/g, '').replace(/\s+/g, ' ');
            const base = String(prop.lhs).replace(/^\s+|\s+$/g, '').replace(/\s+/g, ' ');
            hits.push({ bad, base, kind: 'val' });
            continue;
        }
        const upNode = isUpArrowIndex(atom);
        if (upNode) {
            const bad = String(upNode).replace(/^\s+|\s+$/g, '').replace(/\s+/g, ' ');
            const base = String(upNode.arg).replace(/^\s+|\s+$/g, '').replace(/\s+/g, ' ');
            hits.push({ bad, base, kind: 'uparrow' });
        }
    }
    if (!hits.length) return;
    const show = (s) => (s.length > 40 ? `${s.slice(0, 37)}…` : s);
    const bits = hits.map(({ bad, base }) => `\`${show(base)}\` over \`${show(bad)}\``);
    ctx.warnAst('fin-index-val', node,
        `prefer ${bits.join('; ')} as a Fin GetElem/slice index (avoid \`.val\` and \`↑\`)`,
        1);
}


/**
 * `fin-getelem-app`: a Fin-indexed function (`f : Fin d → α`; predicates `p : Fin d → Prop`
 * included) supports `f[t]` getElem indexing — the `GetElem (Fin n → α) ℕ α` instance from
 * `Instance.Data.Fin.Fun` coerces the Fin index to ℕ and `get_elem_tactic` discharges `t < d`.
 * The bracket form is preferred over `f t` for readability (it also renders as a subscript in
 * LaTeX). When the file does not import `Instance.Data.Fin.Fun` yet, the warning additionally
 * asks for that import so the simplification becomes available.
 */
function finGetElemApp(ctx, sink, decl) {
    const hasImport = !!ctx.scan?.imports?.some((i) => i.module === 'Instance.Data.Fin.Fun');
    const {
        LeanBrace, LeanParenthesis, LeanBracket, LeanColon, Lean_rightarrow,
        LeanArgsSpaceSeparated, LeanToken, LeanRightarrow, LeanLambda,
    } = Lean.classes;
    // Fin-indexed binders of the signature: `(f : Fin d → α)`, `{p q : Fin d → Prop}`, …
    const finNames = new Set();
    for (const n of walk(decl)) {
        if (!(n instanceof LeanColon)) continue;
        const parent = n.parent;
        if (!(parent instanceof LeanParenthesis || parent instanceof LeanBrace || parent instanceof LeanBracket)) continue;
        const type = n.rhs;
        if (!(type instanceof Lean_rightarrow)) continue;
        const domain = type.lhs;
        if (!(domain instanceof LeanArgsSpaceSeparated)) continue;
        const head = domain.args[0];
        if (!(head instanceof LeanToken) || head.text !== 'Fin') continue;
        const names = n.lhs instanceof LeanArgsSpaceSeparated ? n.lhs.args : [n.lhs];
        for (const nm of names) if (nm instanceof LeanToken) finNames.add(nm.text);
    }
    if (!finNames.size) return;
    const suffix = hasImport ? '' : '; add `import Instance.Data.Fin.Fun` to enable the simplification';
    for (const n of walk(decl)) {
        if (!(n instanceof LeanArgsSpaceSeparated) || n.args.length !== 2) continue;
        const head = n.args[0];
        if (!(head instanceof LeanToken) || !finNames.has(head.text)) continue;
        // `{p q : Fin d → Prop}`: a binder's name list is not an application
        if (n.parent instanceof LeanColon && n.parent.lhs === n) continue;
        // `fun f t => …` / `λ f t => …`: a lambda's binder list is not an application
        if (n.parent instanceof LeanRightarrow && n.parent.args[0] === n) continue;
        if (LeanLambda && n.parent instanceof LeanLambda && n.parent.args[0] === n) continue;
        sink.warnAst('fin-getelem-app', n,
            `prefer \`${head.text}[…]\` getElem indexing over \`${head.text} …\` for the Fin-indexed function \`${head.text}\`${suffix}`,
            1);
    }
}



/**
 * Operators whose body is written `op[…](body)`. Those parentheses are the
 * notation's own delimiter and cannot be dropped (`𝔼[x[k]: π](x[k])`).
 */
const RANDOM_NOTATION_OPS = new Set(['𝔼', 'ℙ', '𝕍𝕒𝕣', 'ℂ𝕠𝕧']);

/**
 * Parentheses that close a ℙ / 𝔼 / 𝕍𝕒𝕣 / ℂ𝕠𝕧 notation body.
 * After promote, the paren is `LeanRandomBigOp.scope`. Before promote (ℂ𝕠𝕧 is
 * not promoted today), it is the argument immediately after a GetElem whose
 * head token is one of those operators. Same parent walk as
 * `LeanParenthesis.isProbExpectEventParen`, plus 𝕍𝕒𝕣 / ℂ𝕠𝕧.
 */
function isRandomNotationBodyParen(node) {
    const {
        LeanRandomBigOp,
        LeanGet,
        LeanToken,
        LeanArgsSpaceSeparated,
        LeanProperty,
    } = Lean.classes;
    let self = node;
    let p = node.parent;
    // trailing projection on an unpromoted body: `op[…](x[k]).toReal`
    if (LeanProperty && p instanceof LeanProperty && p.args[0] === node) {
        self = p;
        p = p.parent;
    }
    if (LeanRandomBigOp && p instanceof LeanRandomBigOp && p.scope === self) return true;
    if (!(p instanceof LeanArgsSpaceSeparated)) return false;
    const i = p.args.indexOf(self);
    if (i <= 0) return false;
    const head = p.args[i - 1];
    if (!(head instanceof LeanGet)) return false;
    const base = head.lhs ?? head.args?.[0];
    if (!(base instanceof LeanToken)) return false;
    return RANDOM_NOTATION_OPS.has(base.text);
}

/**
 * `(x[t])` / `(x[t:])` / `(name[t])`: a single parenthesis pair whose only content is a
 * GetElem / slice. GetElem binds tightly enough that the parens never change the parse
 * (`f (x[t])` == `f x[t]`; contrast `(f x)[t]`, whose arg is an application, not GetElem).
 * Skips the body delimiters of ℙ / 𝔼 / 𝕍𝕒𝕣 / ℂ𝕠𝕧 (`𝔼[x[k]: π](x[k])` does not parse
 * without them). Not an AGENTS.md rule (user request).
 */
function parenGetElem(ctx, node) {
    const { LeanParenthesis, LeanGet } = Lean.classes;
    if (!(node instanceof LeanParenthesis)) return;
    const arg = node.arg;
    if (!(arg instanceof LeanGet)) return;
    // tuples / cdot sections keep their parentheses even if nested oddly
    if (typeof node.latexParenRequired === 'function' && node.latexParenRequired()) return;
    // macro body delimiters: `latexParenRequired` covers 𝔼 / ℙ only, not 𝕍𝕒𝕣 / ℂ𝕠𝕧
    if (isRandomNotationBodyParen(node)) return;
    const inner = String(arg).replace(/^\s+|\s+$/g, '').replace(/\s+/g, ' ');
    const show = (s) => (s.length > 60 ? `${s.slice(0, 57)}…` : s);
    ctx.warnAst('paren-getelem', node,
        `\`(${show(inner)})\` → \`${show(inner)}\`: parentheses around a GetElem / slice are redundant`,
        1);
}
function isBareName(node) {
    const { LeanToken, LeanProperty } = Lean.classes;
    if (node instanceof LeanToken) return true;
    // dotted const only (`Nat.zero`, `AsPathRV.path`); not `Set.range fun …`
    if (node instanceof LeanProperty) return isBareName(node.lhs) && isBareName(node.rhs);
    return false;
}

/**
 * `f (x)` / `AsPathRV.path (s)`: a juxtaposition argument that is only a parenthesized bare
 * identifier / dotted const. Application binds tightly enough that the parens never change the
 * parse (`f (x)` == `f x`; contrast `f (x + 1)` / `g (f x)` / `BddAbove (Set.range fun …)`,
 * which need them). Skips `open Namespace (name)` lists. Not an AGENTS.md rule (user request).
 * Emitter note: `*.echo.lean` still prints these from Lean codegen (out of JS scope); this lint
 * catches handwritten sources.
 */
function parenAppArg(ctx, node) {
    const { LeanParenthesis, LeanArgsSpaceSeparated, Lean_open } = Lean.classes;
    if (!(node instanceof LeanParenthesis)) return;
    const parent = node.parent;
    // only a trailing arg of a space-separated application (not the head, not binders/tuples)
    if (!(parent instanceof LeanArgsSpaceSeparated) || parent.args[0] === node) return;
    // `open Finset (range)`: the only-import list parens are required
    for (let p = parent; p; p = p.parent) {
        if (Lean_open && p instanceof Lean_open) return;
    }
    if (typeof node.latexParenRequired === 'function' && node.latexParenRequired()) return;
    const arg = node.arg;
    if (!isBareName(arg)) return;
    const inner = String(arg).replace(/^\s+|\s+$/g, '').replace(/\s+/g, ' ');
    const show = (s) => (s.length > 60 ? `${s.slice(0, 57)}…` : s);
    ctx.warnAst('paren-apparg', node,
        `\`(${show(inner)})\` → \`${show(inner)}\`: parentheses around a bare identifier / const app argument are redundant`,
        1);
}


/**
 * Binder / type ascription whose type is a bare ASCII number-type name:
 * `(s : Real)` / `{n : Nat}` / `(0 : Int)` → prefer Unicode `ℝ` / `ℕ` / `ℤ` / `ℚ` / `ℂ` / `ℝ*`.
 * Only when the ascription type is exactly that token (not `Real → Real`, `Set Real`, `Real.chiSquare`,
 * `import Real.…`, or `open Real`). Not an AGENTS.md rule (Body via Real / @js).
 */
const ASCII_TYPE = Object.freeze({
    Nat: 'ℕ',
    Int: 'ℤ',
    Rat: 'ℚ',
    Real: 'ℝ',
    Complex: 'ℂ',
    Hyperreal: 'ℝ*',
});

function preferUnicodeType(ctx, node) {
    const { LeanColon, LeanToken, LeanParenthesis, LeanBrace } = Lean.classes;
    if (!(node instanceof LeanParenthesis || node instanceof LeanBrace)) return;
    const colon = node.arg;
    if (!(colon instanceof LeanColon)) return;
    const ty = colon.rhs;
    if (!(ty instanceof LeanToken)) return;
    const uni = ASCII_TYPE[ty.text];
    if (!uni) return;
    const shown = quote(node, 80, 1);
    const open = node instanceof LeanBrace ? '{' : '(';
    const close = node instanceof LeanBrace ? '}' : ')';
    const lhs = String(colon.lhs).replace(/^\s+|\s+$/g, '').replace(/\s+/g, ' ');
    const suggest = `${open}${lhs} : ${uni}${close}`;
    ctx.warnAst('prefer-unicode-type', node,
        `\`${shown}\` → \`${suggest}\`: prefer Unicode type in binder / ascription`,
        1);
}

/** does the reprint hold a space outside brackets/parentheses (an application or infix operand)? */
function hasTopLevelSpace(text) {
    let depth = 0;
    for (const c of String(text ?? '')) {
        if ('([{⟨'.includes(c)) depth++;
        else if (')]}⟩'.includes(c)) depth--;
        else if (c === ' ' && depth <= 0) return true;
    }
    return false;
}

const SUPERSCRIPT_POW = { 2: '²', 3: '³', 4: '⁴' };

/**
 * `prefer-unicode-pow`: `x ^ 2` / `x ^ 3` / `x ^ 4` → `x²` / `x³` / `x⁴`. The exponent must be the
 * literal `2` / `3` / `4` (parentheses allowed). The base must be one term: postfix `²` binds to the
 * last atom, so `f x ^ 2` is skipped (`f x²` would be `f (x²)`). Not an AGENTS.md rule (user request).
 */
function preferUnicodePow(ctx, node) {
    const { LeanPow, LeanToken } = Lean.classes;
    if (!(node instanceof LeanPow)) return;
    const exp = unwrapParens(node.rhs);
    if (!(exp instanceof LeanToken)) return;
    const sup = SUPERSCRIPT_POW[exp.text];
    if (!sup) return;
    const base = String(node.lhs ?? '').replace(/^\s+|\s+$/g, '').replace(/\s+/g, ' ');
    if (!base || hasTopLevelSpace(base)) return;
    const show = (s) => (s.length > 60 ? `${s.slice(0, 57)}…` : s);
    ctx.warnAst('prefer-unicode-pow', node,
        `\`${show(`${base} ^ ${exp.text}`)}\` → \`${show(base + sup)}\`: write \`… ^ ${exp.text}\` with the postfix \`${sup}\``,
        1);
}

/**
 * `literal-left-comparison`: a comparison whose left operand is a numeric literal and whose right
 * operand is a variable (`2 ≤ n`) — write `n ≥ 2` instead. Only the four inequalities are
 * reversible (`≤ ↔ ≥`, `< ↔ >`); `=` / `≠` and filtered relations (`≤ᵐ[μ]`) stay quiet, and so
 * do compound operands (`2 ≤ n + 1`, `(1 : ℝ) < n`). Only lemma/theorem signatures
 * (given hypotheses and the conclusion) are inspected — proof bodies are ignored.
 * Warn only; the source is not rewritten.
 * Not an AGENTS.md rule (user request via Random).
 */
const FLIP_COMPARISON = { '≤': '≥', '≥': '≤', '<': '>', '>': '<' };
const NOT_A_VARIABLE = new Set(['this', '_']);

function literalLeftComparison(ctx, node) {
    const { LeanRelational, LeanToken } = Lean.classes;
    if (!(node instanceof LeanRelational)) return;
    const flip = FLIP_COMPARISON[node.operator];
    if (!flip || node.superscript) return;
    const lhs = unwrapParens(node.lhs);
    const rhs = unwrapParens(node.rhs);
    if (!(lhs instanceof LeanToken) || !(rhs instanceof LeanToken)) return;
    const digit = lhs.text;
    if (!/^\d+$/.test(digit)) return;
    const name = rhs.text;
    if (!/^\p{Ll}[\p{L}\p{N}_'!?]*$/u.test(name) || NOT_A_VARIABLE.has(name)) return;
    ctx.warnAst('literal-left-comparison', node,
        `\`${digit} ${node.operator} ${name}\` → \`${name} ${flip} ${digit}\`: write comparisons as \`(variable operator digit)\`; put the variable before the operator and the digit after it`,
        1);
}

/**
 * `range-binder`: a `Finset.range` binder is written with the `<` binder, for big operators and for
 * quantifiers:
 *
 *   ∑ i ∈ Finset.range n, f i  →  ∑ i < n, f i      (likewise `∏`, `⋃`, `⋂`, `⨆`, `⨅`)
 *   ∀ i ∈ Finset.range n, P i  →  ∀ i < n, P i      (likewise `∃`, `∃!`)
 *
 * The `<` form is real notation on both sides: Mathlib's `processBigOpBinder`
 * (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`) maps the big-operator `<` binder to
 * `Finset.Iio n` (and `≤` to `Iic`, …), Lean core's `binderPred` notation
 * (`Init/BinderPredicates.lean`) gives `∀ x < n, …` / `∃ x < n, …` their implication / conjunction
 * form, and Mathlib's `∃!` notation (`Mathlib/Basic/ExistsUnique.lean`) supports any
 * `binder_predicate`, so all of `∑` / `∏` / `⋃` / `⋂` / `⨆` / `⨅` / `∀` / `∃` / `∃!` are covered.
 *
 * WARNING ONLY, no `--fix`: the `<` form is only propositionally equal to the `Finset.range` form,
 * never `rfl`, so a syntax-only rewrite changes the elaborated term and can break proofs:
 * - big operator: `<` elaborates to `Finset.Iio n`, and `Nat.Iio_eq_range : Iio n = range n` is
 *   propositional, so e.g. `rw [AddSumS]` on a lemma stated with `range` finds no occurrence after
 *   the rewrite; converting needs `simp only [Nat.Iio_eq_range]` before the `rw`.
 * - quantifier: `∀ x ∈ s` is membership form (an explicit `→`), `∀ x < n` is implication form; a
 *   proof that feeds the hypothesis to a lemma expecting `∀ x ∈ s` (e.g. `Finset.sum_congr rfl h`)
 *   needs a bridge such as `fun i hi => h i (by simpa using hi)`.
 *
 * Only a literal `Finset.range <arg>` binder set is matched (also the unqualified `range <arg>`): a
 * set difference (`Finset.range n \ {i}`), `Ico` / `Iic` / `Ioi`, `Set.range`, and `Finset.range`
 * used as a plain term are not flagged. `∑'` (tsum) and `∫` are excluded because their notation has
 * no `<` binder, so the suggestion would not parse. Not an AGENTS.md rule (user request).
 */
const RANGE_BINDER_OPS = new Set(['∑', '∏', '⋃', '⋂', '⨆', '⨅', '∀', '∃', '∃!']);

/** the argument of `Finset.range n` / `range n` (one parenthesis pair peeled), or null */
function rangeBinderArgument(node) {
    const { LeanParenthesis, LeanArgsSpaceSeparated, LeanProperty, LeanToken } = Lean.classes;
    const peel = (n) => {
        let x = n;
        while (x instanceof LeanParenthesis) x = x.arg ?? x.args?.[0];
        return x;
    };
    const app = peel(node);
    if (!(app instanceof LeanArgsSpaceSeparated) || app.args.length !== 2) return null;
    const head = peel(app.args[0]);
    const isRange =
        (head instanceof LeanToken && head.text === 'range') ||
        (head instanceof LeanProperty &&
            head.lhs instanceof LeanToken && head.lhs.text === 'Finset' &&
            head.rhs instanceof LeanToken && head.rhs.text === 'range');
    return isRange ? peel(app.args[1]) : null;
}

/** binder slots of a big operator / quantifier: `i ∈ s`, or a group `(i ∈ s) (j ∈ t)` */
function* binderSlots(bound) {
    const { LeanParenthesis, LeanBrace, LeanBracket, LeanArgsSpaceSeparated } = Lean.classes;
    if (!bound) return;
    if (bound instanceof LeanArgsSpaceSeparated) {
        for (const part of bound.args) {
            if (isTrivia(part)) continue;
            yield* binderSlots(part);
        }
        return;
    }
    if (bound instanceof LeanParenthesis || bound instanceof LeanBrace || bound instanceof LeanBracket) {
        yield* binderSlots(bound.arg ?? bound.args?.[0]);
        return;
    }
    yield bound;
}

function rangeBinder(ctx, node) {
    const { LeanBigOperator, Lean_in } = Lean.classes;
    if (!(node instanceof LeanBigOperator)) return;
    const op = node.operator;
    if (!RANGE_BINDER_OPS.has(op)) return;
    const hits = [];
    for (const slot of binderSlots(node.bound)) {
        if (!(slot instanceof Lean_in)) continue;
        const arg = rangeBinderArgument(slot.rhs);
        if (arg) hits.push({ slot, arg });
    }
    if (!hits.length) return;
    // lean.js does not lex `"…"` as a string literal, so text inside a string parses as code (a
    // `"∑ i ∈ Finset.range n, f i"` mention reaches the tree as a big operator whose reprint keeps
    // the closing quote: `∑ i ∈ Finset.range n, f i "`). Such a reprint contains `"`; a real binder
    // written by hand does not, so skip those parser artifacts. (Mentions in comments are comment
    // nodes already, never big operators / quantifiers.)
    if (String(node).includes('"')) return;
    const norm = (s) => s.replace(/\s+/g, ' ').replace(/^\s+|\s+$/g, '');
    const before = norm(String(node.bound));
    let after = before;
    for (const { slot, arg } of hits) {
        const from = norm(String(slot));
        const to = `${norm(String(slot.lhs))} < ${norm(String(arg))}`;
        if (after.includes(from)) after = after.replace(from, to);
    }
    // quote just the operator + binder (not the whole body: the body may be formatted over several lines,
    // and the truncated one-line reprint of the full statement is often not findable in the source).
    // `sequential` finds the n-th identical spelling in the comment/string-blanked source: the tree is in
    // source order, so a file with many equal `∑ k ∈ Finset.range (m + 1)` binders still gets correct lines.
    ctx.warnAst('range-binder', node,
        `\`${op} ${before}\` → \`${op} ${after}\`: a \`Finset.range\` binder is written with \`<\``,
        1, null, `${op} ${before}`, null, true);
}

/**
 * `(h : (T))`: the type of an explicit binder is already a complete term; an outer parenthesis
 * pair around it is redundant against the binder's closing `)` (`(hMs : (sup[…] e < ∞))` →
 * `(hMs : sup[…] e < ∞)`). Keep ascriptions `(e : τ)`, tuples, and `·` sections. Not an AGENTS.md
 * rule (user request).
 */
function parenRedundantType(ctx, node) {
    const { LeanParenthesis, LeanColon } = Lean.classes;
    if (!(node instanceof LeanParenthesis)) return;
    const colon = node.parent;
    // binder `(names : type)` — the type node is this parenthesis
    if (!(colon instanceof LeanColon) || colon.rhs !== node) return;
    if (!(colon.parent instanceof LeanParenthesis)) return;
    // `(h : (e : τ))` / `(h : (⟨…⟩ : τ))` — ascription needs the paren pair
    if (node.arg instanceof LeanColon) return;
    // tuples `(a, b)` / cdot sections `(· + 1)`
    if (typeof node.latexParenRequired === 'function' && node.latexParenRequired()) return;
    const inner = String(node.arg).replace(/^\s+|\s+$/g, '').replace(/\s+/g, ' ');
    const show = (s) => (s.length > 60 ? `${s.slice(0, 57)}…` : s);
    ctx.warnAst('paren-redundant-type', node,
        `\`(${show(inner)})\` → \`${show(inner)}\`: redundant parentheses around binder type`,
        1);
}


/**
 * `((i : ℕ) - (∑ t ∈ s, d t))` / `a - (∏ …)`: parentheses wrapping a ∑/∏ that is already the
 * entire RHS of binary `-` are redundant — the binder scopes the body, and `-`'s RHS is the
 * whole big operator (`a - ∑ t ∈ s, d t`). Do NOT warn for `(∑ …) + d k`: dropping those parens
 * can change meaning (`∑ …, d t + d k`). Not an AGENTS.md rule (user request via Matrix/Body).
 */
function parenRedundantSumSub(ctx, node) {
    const { LeanParenthesis, LeanSub, Lean_sum, Lean_prod } = Lean.classes;
    if (!(node instanceof LeanParenthesis)) return;
    const inner = node.arg;
    if (!(inner instanceof Lean_sum || inner instanceof Lean_prod)) return;
    const parent = node.parent;
    // only the RHS of binary `-` (never `+` / `*` / LHS)
    if (!(parent instanceof LeanSub) || parent.rhs !== node) return;
    if (typeof node.latexParenRequired === 'function' && node.latexParenRequired()) return;
    const text = String(inner).replace(/^\s+|\s+$/g, '').replace(/\s+/g, ' ');
    const show = (s) => (s.length > 60 ? `${s.slice(0, 57)}…` : s);
    ctx.warnAst('paren-redundant-sum-sub', node,
        `\`(${show(text)})\` → \`${show(text)}\`: parentheses around ∑/∏ on the RHS of \`-\` are redundant`,
        1);
}


/**
 * `((a - b) ^ 2)` / `((a + b) ^ n)`: outer parentheses around a `^` whose base is already
 * parenthesized are redundant whenever the parent does not need them for precedence
 * (sum body, `*`/`/`/`+`/`-` operand, relational side, ...). Keep them as an application
 * argument (`f ((a - b) ^ 2)`), property base (`((a - b) ^ 2).foo`), GetElem base,
 * nested-pow LHS (`((a - b) ^ 2) ^ 3`), or the left operand of `@`
 * (`((γ * ℓ) ^ id) @ r`). `^` is `infixr:80` and `@` is `infixl:70`, so dropping the
 * outer parens parses as `(γ * ℓ) ^ (id @ r)`. Fisher imply / SB pattern. Not an
 * AGENTS.md rule (user request via Random / @js).
 */
function parenRedundantPow(ctx, node) {
    const {
        LeanParenthesis, LeanPow, LeanArgsSpaceSeparated, LeanProperty,
        LeanGet, LeanGetElemQue, LeanGetElemQuote, LeanColon, LeanMatMul,
    } = Lean.classes;
    if (!(node instanceof LeanParenthesis)) return;
    const pow = node.arg;
    if (!(pow instanceof LeanPow)) return;
    // base already parenthesized: ((sub) ^ 2); bare (x ^ 2) stays quiet
    if (!(pow.lhs instanceof LeanParenthesis)) return;
    if (typeof node.latexParenRequired === 'function' && node.latexParenRequired()) return;
    const parent = node.parent;
    // `((base) ^ exp) arg` -- application binds tighter than `^`, so the outer parens
    // keep `arg` out of the exponent (`((γ * ℓ) ^ (id : ℕ → ℕ)) k`).
    // `f ((a - b) ^ 2)` -- juxtaposition argument also needs the paren.
    if (parent instanceof LeanArgsSpaceSeparated) return;
    // ((a - b) ^ 2).foo
    if (parent instanceof LeanProperty && parent.lhs === node) return;
    // ((a - b) ^ 2)[i]
    if (parent instanceof LeanGet && parent.lhs === node) return;
    if (LeanGetElemQue && parent instanceof LeanGetElemQue && parent.lhs === node) return;
    if (LeanGetElemQuote && parent instanceof LeanGetElemQuote && parent.args?.[0] === node) return;
    // ((a - b) ^ 2) ^ 3 -- right-assoc without paren
    if (parent instanceof LeanPow && parent.lhs === node) return;
    if (parent instanceof LeanColon) return;
    // ((γ * ℓ) ^ id) @ r — outer parens keep `@` outside the power
    if (parent instanceof LeanMatMul && parent.args[0] === node) return;
    const text = String(pow).replace(/^\s+|\s+$/g, '').replace(/\s+/g, ' ');
    const show = (s) => (s.length > 60 ? `${s.slice(0, 57)}…` : s);
    ctx.warnAst('paren-redundant-pow', node,
        `\`(${show(text)})\` → \`${show(text)}\`: outer parentheses around \`… ^ …\` are redundant`,
        1);
}

/**
 * Needless parentheses around an arithmetic operand when dropping them does not change the
 * parse (`(μ * Δx) * (∂[t, t] u t x)` → `μ * Δx * ∂[t, t] u t x`).
 *
 * - Parent is a binary `LeanArithmetic` (`*`, `/`, `+`, `-`, `^`, …).
 * - Skip ascriptions `(e : τ)`, tuples, `·` sections (`latexParenRequired`).
 * - Child arithmetic with strictly higher priority: both sides (`(a * b) + c`, `a + (b * c)`).
 * - Same priority, left-assoc (`*`/`/`/`+`/`-`): only the LHS (`(a * b) * c`; not `a * (b * c)`).
 * - Same priority, right-assoc (`^`): only the RHS (`a ^ (b ^ c)`).
 * - `Lean_partial`: only as the RHS of `*`/`/` (LHS would swallow the operator into the partial
 *   scope: `∂[t] u * μ` ≠ `(∂[t] u) * μ`).
 * - Space-separated application: both sides of `*`/`/` (`(f x) * g`, `f * (g x)`).
 * - Skip repo `⬝ᵥ` (`Dot.dot` via `pathDotV` / `infixl:72 (priority := 2000)`, Mathlib `dotProduct` fallback)
 *   as the parent or the parenthesized child (Random / importance_sampling: dropping those parens does not compile).
 * - Skip when the parenthesized child's right spine ends at `fun` (the lambda would swallow
 *   a following `=`, `|`, or `:=`).
 * - Skip parens around a `•` (`SMul` / `Lean_bullet`, priority 73) that is the
 *   numerator of `/` (priority 70): dropping them previously broke `field_simp` in
 *   `is_weight_eq_score` (Random / importance_sampling).
 *
 * Not an AGENTS.md rule (user request via Hyperreal / Body).
 */
/** Repo `⬝ᵥ` (`Dot.dot`): `pathDotV` in `Instance/Data/Vector/Basic/Dot.lean` tries `Dot.dot` first
 * (path tsums, no `Fintype`), then falls back to Mathlib `dotProduct`. Also
 * `infixl:72 (priority := 2000) " ⬝ᵥ " => Dot.dot`. Not a `*`/`+`-style operator for this rule. */
function isDotV(node) {
    const { Lean_cdotp } = Lean.classes;
    return !!Lean_cdotp && node instanceof Lean_cdotp && node.subscript === 'ᵥ';
}

/** `•` (`SMul`): `Lean_bullet`, priority 73. */
function isSMul(node) {
    const { Lean_bullet } = Lean.classes;
    return !!Lean_bullet && node instanceof Lean_bullet;
}

/** `∑` / `∑'` / `∏` (and tsum/tprod variants): the binder comma swallows following `+` / `-`. */
function isBigOp(node) {
    const { Lean_sum, Lean_prod, Lean_tsum, Lean_tprod } = Lean.classes;
    if (!node) return false;
    if (Lean_sum && node instanceof Lean_sum) return true;
    if (Lean_prod && node instanceof Lean_prod) return true;
    if (Lean_tsum && node instanceof Lean_tsum) return true;
    if (Lean_tprod && node instanceof Lean_tprod) return true;
    return false;
}

/** Parenthesized arith whose operands are (or unwrap to) big operators. */
function arithContainsBigOp(node) {
    const { LeanParenthesis, LeanArithmetic } = Lean.classes;
    const seen = new Set();
    const walk = (n) => {
        if (!n || seen.has(n)) return false;
        seen.add(n);
        if (n instanceof LeanParenthesis) return walk(n.arg);
        if (isBigOp(n)) return true;
        if (n instanceof LeanArithmetic) return walk(n.lhs) || walk(n.rhs);
        return false;
    };
    return walk(node);
}

/** Right spine ends at `fun`: dropping parens lets the lambda swallow following `=`, `|`, `:=`. */
function rightSpineEndsWithFun(node) {
    const { LeanArithmetic, LeanParenthesis, Lean_fun } = Lean.classes;
    for (let n = node; n; ) {
        if (Lean_fun && n instanceof Lean_fun) return true;
        if (n instanceof LeanParenthesis) { n = n.arg; continue; }
        if (n instanceof LeanArithmetic && n.rhs != null) { n = n.rhs; continue; }
        return false;
    }
    return false;
}

/**
 * Structural equality of two parse trees, ignoring `LeanParenthesis` wrappers (parentheses never
 * change the shape of the parse; they only record that the source had them).
 */
function sameShape(a, b) {
    const { LeanParenthesis, LeanToken } = Lean.classes;
    let x = a;
    let y = b;
    while (x instanceof LeanParenthesis) x = x.arg;
    while (y instanceof LeanParenthesis) y = y.arg;
    if (x === y) return true;
    if (!x || !y || typeof x !== 'object' || typeof y !== 'object') return false;
    if (x.constructor?.name !== y.constructor?.name) return false;
    if (x instanceof LeanToken) return x.text === y.text;
    // scalar flags that change the printed operator (`ᵥ*`, `×ₖ`, `⊗ₘ`, …)
    for (const k of ['subscript', 'superscript', 'modifier', 'isLeftSubscript'])
        if ((x[k] ?? null) !== (y[k] ?? null)) return false;
    const ax = Array.isArray(x.args) ? x.args : [];
    const ay = Array.isArray(y.args) ? y.args : [];
    if (ax.length !== ay.length) return false;
    for (let i = 0; i < ax.length; i++) if (!sameShape(ax[i], ay[i])) return false;
    return true;
}

/**
 * `∀ (k : ℕ), p k` → `∀ k : ℕ, p k`, and likewise `∃ (k : ℕ), p k` → `∃ k : ℕ, p k`
 * and `fun (k : ℕ) => k` → `fun k : ℕ => k`: a single explicitly typed binder needs no
 * parentheses — `∀` / `∃` bind the annotation up to the comma, and `fun` up to `=>`.
 * Only the single-binder form is rewritten: `∀ (x : α) (y : β), b` / `∃ (x : α) (y : β), p` /
 * `fun (x : α) (y : β) => b` must keep their parens (dropping them changes the parse,
 * `α y : β`), so a multi-binder `LeanArgsSpaceSeparated` is left alone.
 * `∀ (x y : α), b` is one binder group and becomes `∀ x y : α, b`.
 * Untyped binders and binders with `∈` are out of scope. Not an AGENTS.md rule (user request).
 */
function parenRedundantBinder(ctx, node) {
    const { Lean_forall, Lean_exists, Lean_fun, LeanParenthesis, LeanColon, LeanToken, LeanArgsSpaceSeparated, LeanRightarrow } = Lean.classes;
    let bound;
    // `∀` / `∃` keep the binder in `bound`; a lambda keeps it on the left of its arrow
    if (node instanceof Lean_forall || node instanceof Lean_exists) bound = node.bound;
    else if (node instanceof Lean_fun) {
        const arrow = node.arg;
        if (!(arrow instanceof LeanRightarrow)) return;
        bound = arrow.lhs;
    } else return;
    // exactly one binder, written `(names : type)`; several binder groups (`∀ (x : α) (y : β)`)
    // are a LeanArgsSpaceSeparated and stay parenthesized
    if (!(bound instanceof LeanParenthesis)) return;
    const colon = bound.arg;
    if (!(colon instanceof LeanColon)) return;
    // binder names must be bare identifiers (`(x : α)` / `(x y : α)`); other shapes keep their parens
    const names = colon.lhs instanceof LeanArgsSpaceSeparated ? colon.lhs.args : [colon.lhs];
    if (!names.length || !names.every((n) => n instanceof LeanToken)) return;
    if (typeof bound.latexParenRequired === 'function' && bound.latexParenRequired()) return;
    const full = String(node).replace(/\s+$/, '');
    const boundText = String(bound);
    const at = full.indexOf(boundText);
    // the reprint must show the binder verbatim, or the suggestion cannot be spelled exactly
    if (at < 0) return;
    const before = full.replace(/\s+/g, ' ').trim();
    const after = (full.slice(0, at) + String(colon) + full.slice(at + boundText.length)).replace(/\s+/g, ' ').trim();
    const show = (s) => (s.length > 80 ? `${s.slice(0, 77)}…` : s);
    ctx.warnAst('paren-redundant-binder', node,
        `\`${show(before)}\` → \`${show(after)}\`: redundant parentheses around a typed binder`,
        2);
}

function parenRedundantArith(ctx, node) {
    const {
        LeanParenthesis, LeanArithmetic, LeanBigOperator, LeanDiv, LeanColon,
        Lean_sqrt, LeanPow, LeanUnaryArithmeticPost,
    } = Lean.classes;
    if (!(node instanceof LeanParenthesis)) return;
    const arg = node.arg;
    const parent = node.parent;
    if (parent instanceof Lean_sqrt) {
        const group = parent.parent;
        const power = group?.parent;
        if (group instanceof LeanParenthesis && power instanceof LeanUnaryArithmeticPost && isBareName(arg)) {
            ctx.warnAst('paren-redundant-arith', power,
                'Parentheses around the atomic square-root argument are redundant inside the grouped power',
                1, null, null, { fix: { text: String(power), mode: 'sqrt-argument' } });
        }
        return;
    }
    if (typeof node.latexParenRequired === 'function' && node.latexParenRequired()) return;
    // `(μ : ℝ*)` ascriptions stay
    if (arg instanceof LeanColon) return;
    // `if` / `fun` / `let` / `match` / `by` / tuples: the extent of these forms is not captured by
    // the parser's arithmetic insert below, so keep the parens (also covers `(fun y => f y) - g`).
    const head = unwrapParens(arg);
    if (head && ASCRIPTION_KEEP_PARENS.has(head.constructor?.name || '')) return;
    if (!(parent instanceof LeanArithmetic)) return;
    // lean.js can attach a postfix power after the entire product in `a * (√(x))²`.
    // Keep the root grouped when dropping the pair would expose it to that power.
    if (head instanceof Lean_sqrt && (parent instanceof LeanPow ||
        (parent.rhs === node && parent.parent instanceof LeanUnaryArithmeticPost))) return;
    // `⬝ᵥ` is this repo's `Dot.dot` (`pathDotV` / `infixl:72`), not `*`/`+`. Parens around a
    // `⬝ᵥ` parent stay: a trailing `fun` in its RHS swallows following `=`, `|`, `:=`, and
    // `γ ^ range (k + 1) ⬝ᵥ v` takes `range (k + 1)` as the `Dot.dot` argument.
    // (A `⬝ᵥ` *operand* is handled by the `stack_priority` guard below plus the re-parse.)
    if (isDotV(parent)) return;
    if (rightSpineEndsWithFun(arg)) return;
    // Big-operator binder commas (`∑ x ∈ s, …`, `∑'`, `∏`) swallow following `+` / `-`.
    // The AST reprint often parenthesizes each sum (`((∑ …) - (∑ …))`) even when the source
    // only groups the whole difference, e.g. `|(∑ … - ∑ …) + …|`. Dropping those source
    // parens changes the parse; the reprint also fails `locate` (no source line).
    if (arithContainsBigOp(arg)) return;
    // unary arith (Neg/…) keep their operand grouping decisions elsewhere
    if (parent.lhs == null || parent.rhs == null) return;
    const onLhs = parent.lhs === node;
    const onRhs = parent.rhs === node;
    if (!onLhs && !onRhs) return;
    // Parens around a `•` (`SMul`) numerator of `/` are required in this repo:
    // dropping them previously broke `field_simp` in `is_weight_eq_score`
    // (Random / importance_sampling), even though `•` is priority 73 and `/` is 70.
    if (parent instanceof LeanDiv && onLhs && isSMul(arg)) return;

    // `∇[x] …` / `∂[t] …` / `∫ …` / `𝔼 …` term macros parse their body at a fixed precedence
    // (`term:67`), and `⬝ᵥ` is `infixl:72`: a following operator that binds tighter is swallowed
    // into them. This parser models that extent as `stack_priority`; keep the parens when the
    // operator (or, on the RHS, an ancestor that takes the parent as its LHS) outranks it.
    if (isDotV(head) || (LeanBigOperator && head instanceof LeanBigOperator)) {
        const sNode = head.stack_priority ?? head.constructor.input_priority ?? 100;
        const pOp = parent.constructor.input_priority ?? 0;
        if (pOp > sNode) return;
        const up = parent.parent;
        if (onRhs && up instanceof LeanArithmetic && up.lhs === parent && (up.constructor.input_priority ?? 0) > sNode) return;
    }

    // Re-parse the parent with and without this paren pair: redundant iff the trees coincide.
    // This covers repo term macros (`∇[x] …`, `∂[x] …`, `∑ …`), applications, and nested binary
    // chains without a precedence table, and stays conservative for lambdas / `if` / `let` / `match`.
    const op = parent.operator;
    if (typeof op !== 'string' || !op) return;
    const inner = String(arg).replace(/^\s+|\s+$/g, '');
    const lhsWith = onLhs ? `(${inner})` : String(parent.lhs);
    const rhsWith = onRhs ? `(${inner})` : String(parent.rhs);
    const parsedWith = parseTermNode(`${lhsWith} ${op} ${rhsWith}`);
    const parsedWithout = parseTermNode(`${onLhs ? inner : lhsWith} ${op} ${onRhs ? inner : rhsWith}`);
    if (!parsedWith || !parsedWithout) return;
    if (!sameShape(parsedWith, parsedWithout)) return;

    const text = inner.replace(/\s+/g, ' ');
    const show = (s) => (s.length > 60 ? `${s.slice(0, 57)}…` : s);
    ctx.warnAst('paren-redundant-arith', node,
        `\`(${show(text)})\` → \`${show(text)}\`: parentheses are redundant here`,
        1, null, null, { fix: { text: String(node), mode: 'outer' } });
}

/**
 * `((expr) : Type)` → `(expr : Type)`: the ascribed value is already parenthesized by the
 * ascription, so the inner pair is redundant. Conservative: the parens are only dropped when
 * re-parsing `(value : type)` reproduces the very same ascription, and the value is not a form
 * whose parens are load-bearing (lambda, `if`, `by`, tuple, structure literal, nested ascription,
 * match, `let`, `do`, `calc`, …). `(((e)) : T)` drops every inner pair. Not an AGENTS.md rule
 * (user request via Real / Softmax).
 */
function parenRedundantAscription(ctx, node) {
    const { LeanParenthesis, LeanColon } = Lean.classes;
    if (!(node instanceof LeanParenthesis)) return;
    const colon = node.arg;
    if (!(colon instanceof LeanColon)) return;
    const inner = colon.lhs;
    if (!(inner instanceof LeanParenthesis)) return;
    if (typeof inner.latexParenRequired === 'function' && inner.latexParenRequired()) return;
    const value = unwrapParens(inner);
    if (!value) return;
    if (ASCRIPTION_KEEP_PARENS.has(value.constructor?.name || '')) return;
    // re-parse the shortened spelling: it must still be the same ascription
    const type = String(colon.rhs);
    const parsed = unwrapParens(parseTermNode(`(${String(value)} : ${type})`));
    if (!(parsed instanceof LeanColon)) return;
    if (collapse(String(parsed.lhs)) !== collapse(String(value))) return;
    if (collapse(String(parsed.rhs)) !== collapse(type)) return;
    const before = `(${String(inner)} : ${type})`;
    const after = `(${String(value)} : ${type})`;
    const show = (s) => (s.length > 60 ? `${s.slice(0, 57)}…` : s);
    ctx.warnAst('paren-redundant-ascription', node,
        `\`${show(before)}\` → \`${show(after)}\`: the ascribed value is already inside the ascription's parentheses`,
        1, null, null, { fix: { text: String(node) } });
}

/** is the repo-relative path a `Lemma/…` file? */
export function isLemmaPath(file) {
    return /(^|\/)Lemma\//.test(String(file ?? '').replace(/\\/g, '/'));
}

// ---------------------------------------------------------------------------------------------------------------
// `dot-notation`: `N.f x` → `x.f` when `x`'s declared type head is `N`.

/** binder body of a `(…)` / `{…}` / `[…]` group (a one-element wrapper is transparent) */
function binderInner(node) {
    const { LeanParenthesis, LeanBrace, LeanBracket, LeanArgsSpaceSeparated } = Lean.classes;
    let n = node;
    for (;;) {
        if (n instanceof LeanParenthesis || n instanceof LeanBrace || n instanceof LeanBracket) n = n.arg ?? n.args?.[0];
        else if (n instanceof LeanArgsSpaceSeparated && n.args.length === 1) n = n.args[0];
        else return n;
    }
}

/**
 * `(a b : T)` / `{d : ℕ}` / `(i : Fin n)` → `[{ name, type }]`; an unannotated binder
 * (`∑ t, …`, `fun t => …`) gives `type: null` — unknown types are never guessed.
 */
function typedBinders(node) {
    const { LeanColon, LeanToken, LeanArgsSpaceSeparated } = Lean.classes;
    const body = binderInner(node);
    if (body instanceof LeanColon) {
        const lhs = body.lhs instanceof LeanArgsSpaceSeparated ? body.lhs.args : [body.lhs];
        if (!lhs.length || !lhs.every((n) => n instanceof LeanToken)) return [];
        return lhs.map((n) => ({ name: n.text, type: body.rhs }));
    }
    if (body instanceof LeanToken) return [{ name: body.text, type: null }];
    return [];
}

/** identifier head of a type node: `Fin d` → `Fin`, `EuclideanSpace ℝ (Fin n)` → `EuclideanSpace` */
function typeHeadName(type) {
    const { LeanParenthesis, LeanArgsSpaceSeparated, LeanToken } = Lean.classes;
    let n = type;
    for (;;) {
        if (n instanceof LeanParenthesis) n = n.arg ?? n.args?.[0];
        else if (n instanceof LeanArgsSpaceSeparated) n = n.args[0];
        else break;
    }
    return n instanceof LeanToken ? n.text : null;
}

/**
 * A function type lives in the `Function` namespace: `u.Injective` resolves to
 * `Function.Injective u` for any `u` whose declared type is a plain arrow (`α → β`)
 * or a dependent `∀` (`∀ i, P i`). Returns `'Function'` for such a type node
 * (after peeling parens / space-separated applications), else `null`.
 * A bundled-hom arrow carries a subscript / modifier (`→*` MonoidHom, `→ₗ` LinearMap,
 * `→ₐ` AlgHom, `→+` AddMonoidHom) and is its own namespace, where `h.Injective` is not
 * valid Lean, so those stay silent. `⇒` (`fun`/`match`/`by`) is never a type.
 */
function functionTypeHead(type) {
    const { LeanParenthesis, LeanArgsSpaceSeparated, Lean_rightarrow, Lean_forall } = Lean.classes;
    let n = type;
    for (;;) {
        if (n instanceof LeanParenthesis) n = n.arg ?? n.args?.[0];
        else if (n instanceof LeanArgsSpaceSeparated) n = n.args[0];
        else break;
    }
    if (n instanceof Lean_rightarrow) return !n.subscript && !n.modifier ? 'Function' : null;
    if (n instanceof Lean_forall) return 'Function';
    return null;
}

/**
 * Element type of `(θ : Fin n → α)`. `θ[j]` has type `α`, so `α.f θ[j]` is `θ[j].f`
 * for any field. A bare `x : ℝ` does not use this: `Real.sqrt x` stays as written.
 * Unicode codomains match their ASCII namespace (`ℝ`/`Real`, `ℕ`/`Nat`, …).
 * A codomain that is itself a function type (`Fin n → (α → β)`) reports `Function`,
 * so `Function.Injective θ[j]` rewrites to `θ[j].Injective`.
 */
function finArrowElementHead(type) {
    const { LeanParenthesis, Lean_rightarrow } = Lean.classes;
    let n = type;
    while (n instanceof LeanParenthesis) n = n.arg ?? n.args?.[0];
    if (!(n instanceof Lean_rightarrow) || n.args?.length !== 2) return null;
    if (typeHeadName(n.args[0]) !== 'Fin') return null;
    return typeHeadName(n.args[1]) ?? functionTypeHead(n.args[1]);
}

/** Exact head match. A `Fin`-arrow element also accepts the Unicode spelling of `ns`. */
function dotTypeHeadMatches(typeHead, ns, indexed) {
    if (!typeHead) return false;
    if (typeHead === ns) return true;
    return !!indexed && ASCII_TYPE[ns] === typeHead;
}

/** statement / binder containers whose items run in source order */
const DOT_SEQUENCES = new Set(['LeanStatements', 'LeanArgsNewLineSeparated']);

/**
 * The two operand types of `A ⊕ B` → `[A, B]`. The grammar nests `A ⊕ B ≃ C` as
 * `A ⊕ (B ≃ C)` (the `≃` lands in the `⊕` right operand), so that shape is normalized
 * back to `A ⊕ B` — the `toFun` of the enclosing equivalence then has scrutinee `A ⊕ B`.
 */
function sumOperands(type) {
    const { LeanParenthesis, Lean_oplus, Lean_simeq } = Lean.classes;
    let n = type;
    while (n instanceof LeanParenthesis) n = n.arg ?? n.args?.[0];
    if (!(n instanceof Lean_oplus) || n.args?.length !== 2) return null;
    const [left, right] = n.args;
    return [left, right instanceof Lean_simeq ? right.args?.[0] : right];
}

/**
 * `fun | Sum.inl t => … | Sum.inr t => …` over a scrutinee `A ⊕ B`: bind `t` to `A`
 * (left) or `B` (right). Names bound to different heads in the two alternatives stay unknown.
 */
function sumPatternBindings(value, type) {
    const parts = sumOperands(type);
    if (!parts) return null;
    const { LeanArgsSpaceSeparated, LeanProperty, LeanToken } = Lean.classes;
    const bound = new Map();
    const conflicting = new Set();
    const scan = (n) => {
        if (!n || typeof n !== 'object') return;
        if (n instanceof LeanArgsSpaceSeparated && n.args?.length === 2) {
            const [head, arg] = n.args;
            if (head instanceof LeanProperty && head.lhs instanceof LeanToken && head.lhs.text === 'Sum' &&
                head.rhs instanceof LeanToken && (head.rhs.text === 'inl' || head.rhs.text === 'inr') &&
                arg instanceof LeanToken && arg.text) {
                const component = head.rhs.text === 'inl' ? parts[0] : parts[1];
                if (!bound.has(arg.text)) bound.set(arg.text, component);
                else if (typeHeadName(bound.get(arg.text)) !== typeHeadName(component)) conflicting.add(arg.text);
            }
        }
        for (const a of n.args || []) scan(a);
    };
    scan(value);
    for (const name of conflicting) bound.delete(name);
    return bound;
}

/**
 * Generalized field notation: `Ns.f obj` → `obj.f` (`Fin.ropeEven t` → `t.ropeEven`), and for 3+
 * explicit args `Ns.f a1 … ak obj` → `obj.f a1 … ak` (`Fin.castAdd d t` → `t.castAdd d`) when `obj`
 * is the LAST bare-identifier arg whose declared type head is `Ns`, every earlier explicit arg is
 * also a bare identifier, and none of them shares `Ns` as its type head (the receiver slot must be
 * unambiguous — `Fin.h t u` with two `Fin` args is skipped).
 * A 2-arg receiver may also be a GetElem (`α.f θ[j]` → `θ[j].f`) when the base is a binder
 * `(θ : Fin n → α)`. The codomain may be the Unicode type of `Ns` (`ℝ` for `Real`).
 * A receiver whose declared type is itself an arrow or `∀` (`u : α → β`, `f : ∀ i, P i`) is treated
 * as a `Function` namespace member, so `Function.Injective u` → `u.Injective` for any `Function.*`
 * field (the GetElem codomain case extends this: `Function.Injective θ[j]` → `θ[j].Injective`).
 *
 * A scoped environment of local binders → type node is kept in source order (declaration binders,
 * `∑` / `∏` / `∀` / `∃` binder lists, `fun` parameters, typed `let` / `have`); the nearest binding
 * wins (shadowing). Unannotated binders stay unknown, so a pattern binder never warns. Only the
 * declared type *head* is compared (no elaboration); `simp [Fin.ropeEven]` has no argument and is
 * therefore never flagged. Not an AGENTS.md rule (user request).
 */
function dotNotation(ctx, decl) {
    if (/\.echo\.lean$/.test(String(ctx.file ?? ''))) return; // generated by run.mjs
    const {
        LeanAssign, LeanColon, LeanArgsSpaceSeparated, LeanProperty, LeanToken, LeanGet,
        LeanBigOperator, Lean_forall, Lean_exists, Lean_fun, Lean_let, Lean_have, LeanRightarrow,
    } = Lean.classes;
    const env = new Map();

    const checkApplication = (node, scope) => {
        const args = node.args;
        if (!args || args.length < 2) return;
        const head = args[0];
        // two-component dotted constant `Ns.f` applied to one or more explicit arguments
        if (!(head instanceof LeanProperty) || !(head.lhs instanceof LeanToken) || !(head.rhs instanceof LeanToken)) return;
        const ns = head.lhs.text;
        const field = head.rhs.text;
        if (!ns || !field) return;

        const bareToken = (a) => a instanceof LeanToken && a.text && a.text !== '_';

        // 2-arg receiver: a bare identifier, or a GetElem `θ[j]` whose base is one.
        // A slice `θ[:j]` is not the arrow codomain, so it is not a receiver.
        const receiver = (arg) => {
            if (bareToken(arg)) return { name: arg.text, indexed: false, spelling: arg.text };
            if (!(arg instanceof LeanGet)) return null;
            const base = arg.lhs ?? arg.args?.[0];
            const index = arg.rhs ?? arg.args?.[1];
            if (!bareToken(base) || index instanceof LeanColon) return null;
            return { name: base.text, indexed: true, spelling: String(arg).replace(/\s+/g, ' ').trim() };
        };
        const receiverHead = (recv) => {
            const type = scope.get(recv.name);
            if (type == null) return null;
            if (!recv.indexed) return typeHeadName(type) ?? functionTypeHead(type);
            return finArrowElementHead(type);
        };

        // 2-arg: `Ns.f x` — the sole explicit argument is the receiver
        if (args.length === 2) {
            const recv = receiver(args[1]);
            if (!recv || !dotTypeHeadMatches(receiverHead(recv), ns, recv.indexed)) return;
            const shown = String(node).replace(/\s+/g, ' ').trim();
            ctx.warnAst('dot-notation', node, `\`${shown}\` can be written \`${recv.spelling}.${field}\``, 1, null, shown, null, true);
            return;
        }

        // 3+-arg: the receiver is the LAST explicit argument. Generalized field notation only rewrites
        // when the receiver slot is unambiguous: every explicit argument must be a bare identifier (so
        // its declared type head is statically known) and exactly one — the last — has type head `Ns`
        // (`Fin.castAdd d t` → `t.castAdd d`; `Fin.h t u` is skipped because both `t` and `u` are `Fin`).
        const rest = args.slice(1);
        if (!rest.every(bareToken)) return;
        const headOf = (t) => (t == null ? null : typeHeadName(t) ?? functionTypeHead(t));
        const obj = rest[rest.length - 1];
        if (headOf(scope.get(obj.text)) !== ns) return;
        for (const a of rest.slice(0, -1)) {
            if (headOf(scope.get(a.text)) === ns) return; // two `Ns`-typed explicit args: ambiguous
        }
        const front = rest.slice(0, -1).map((a) => String(a).replace(/\s+/g, ' ').trim());
        const shown = String(node).replace(/\s+/g, ' ').trim();
        const rewritten = `${obj.text}.${field}${front.length ? ` ${front.join(' ')}` : ''}`;
        ctx.warnAst('dot-notation', node, `\`${shown}\` can be written \`${rewritten}\``, 1, null, shown, null, true);
    };

    /** bindings a statement introduces for the statements after it (`let t : Fin d := …`) */
    const introducedBinders = (item) => {
        if (!(item instanceof Lean_let) && !(item instanceof Lean_have)) return [];
        const head = item.args?.[0];
        return typedBinders(head instanceof LeanAssign ? head.lhs : head);
    };

    const walkSequence = (node, scope) => {
        const saved = [];
        for (const item of node.args || []) {
            walkTerm(item, scope);
            for (const b of introducedBinders(item)) {
                if (!b.type) continue;
                saved.push([b.name, scope.has(b.name), scope.get(b.name)]);
                scope.set(b.name, b.type);
            }
        }
        for (let i = saved.length - 1; i >= 0; i--) {
            const [name, had, value] = saved[i];
            if (had) scope.set(name, value);
            else scope.delete(name);
        }
    };

    const walkTerm = (node, scope) => {
        if (!node || typeof node !== 'object') return;
        if (node instanceof LeanArgsSpaceSeparated) {
            checkApplication(node, scope);
            for (const a of node.args || []) walkTerm(a, scope);
            return;
        }
        if (DOT_SEQUENCES.has(node.constructor?.name)) {
            walkSequence(node, scope);
            return;
        }
        // `let e : A ⊕ B ≃ C := { toFun := fun | Sum.inl t => … }`: pattern binders
        if (node instanceof Lean_let || node instanceof Lean_have) {
            const head = node.args?.[0];
            if (head instanceof LeanAssign && head.lhs instanceof LeanColon) {
                const patterns = sumPatternBindings(head.rhs, head.lhs.rhs);
                if (patterns?.size) {
                    walkTerm(head.lhs, scope);
                    const inner = new Map(scope);
                    for (const [name, type] of patterns) inner.set(name, type);
                    walkTerm(head.rhs, inner);
                    return;
                }
            }
        }
        if (node instanceof LeanBigOperator || node instanceof Lean_forall || node instanceof Lean_exists) {
            const binder = node.args?.[0];
            const body = node.args?.[1];
            if (binder != null && body != null) {
                walkTerm(binder, scope); // the annotation is outside the binder's scope
                const inner = new Map(scope);
                for (const b of typedBinders(binder)) if (b.type) inner.set(b.name, b.type);
                walkTerm(body, inner);
                return;
            }
        }
        if (node instanceof Lean_fun) {
            const arrow = node.arg ?? node.args?.[0];
            if (arrow instanceof LeanRightarrow) {
                walkTerm(arrow.lhs, scope);
                const inner = new Map(scope);
                for (const b of typedBinders(arrow.lhs)) if (b.type) inner.set(b.name, b.type);
                walkTerm(arrow.rhs, inner);
                return;
            }
        }
        for (const a of node.args || []) walkTerm(a, scope);
    };

    // declaration binders, in order; a binder's type is checked with the binders before it
    const seedSignature = (node) => {
        if (!node || typeof node !== 'object') return;
        if (node instanceof LeanToken) return; // the declaration's own name
        const binders = typedBinders(node);
        if (binders.length) {
            for (const b of binders) if (b.type) walkTerm(b.type, env);
            for (const b of binders) if (b.type) env.set(b.name, b.type);
            return;
        }
        for (const a of node.args || []) seedSignature(a);
    };

    const assign = decl.assignment ?? decl.args?.find((a) => a instanceof LeanAssign);
    const colon = assign instanceof LeanAssign ? assign.lhs : null;
    if (colon instanceof LeanColon) {
        if (colon.lhs) seedSignature(colon.lhs);
        if (colon.rhs) walkTerm(colon.rhs, env);
    }
    if (assign?.rhs) walkTerm(assign.rhs, env);
}

/**
 * `decl-keyword-dir`: a `theorem` in a `Lemma/` file (AGENTS.md: `Lemma/` holds only `lemma`s). The keyword is the
 * node class (`Lean_theorem`), so modifiers (`private`, `noncomputable`, `@[…]`), comments, strings and names like
 * `theorem_foo` never match. Quotes the declaration head (the reprint's line holding the keyword).
 */
function declKeywordDir(ctx, decl) {
    const { Lean_theorem } = Lean.classes;
    if (!(decl instanceof Lean_theorem)) return;
    // the reprint without the `@[…]` prefix (a mis-parsed attribute can swallow the previous declaration)
    let text = String(decl).replace(/^\n+/, '');
    const attr = decl.attribute != null ? String(decl.attribute) : '';
    if (attr && text.startsWith(attr)) text = text.slice(attr.length);
    const lines = text.replace(/^\s+/, '').split('\n');
    const head = (lines.find((l) => /(^|\s)theorem\b/.test(l)) ?? lines[0]).trim();
    const name = declName(decl) ?? /(?:^|\s)theorem\s+([^\s:({[⦃]+)/.exec(head)?.[1];
    const stmt = head.length > 120 ? `${head.slice(0, 120)}…` : head;
    // `compile` stamps the declaration with its 1-based source line. `Lean_def.firstToken`
    // skips a leading `@[…]` attribute, so this is the `theorem` keyword/name line.
    ctx.declHeadLines ??= new Set();
    const line = decl.line ?? locate(ctx.P.raw, stmt, 0);
    if (line == null || ctx.declHeadLines.has(line)) return;
    ctx.declHeadLines.add(line);
    ctx.warn('decl-keyword-dir', line, null, `\`theorem${name ? ` ${name}` : ''}\` in \`Lemma/\`: declare it with \`lemma\``, { stmt });
}

/**
 * `public-section`: `public section` is not used in `Theorem/`. The tree keeps the modifier only when it was
 * written (`kwargs.accessibility` is undefined for a plain `section`), so this never fires on plain sections,
 * nor on `noncomputable section` / `private section`. Warn only; no text fallback (AST only).
 */
function publicSection(ctx, node, inTheorem) {
    const { Lean_section } = Lean.classes;
    if (!(node instanceof Lean_section) || !inTheorem) return;
    const acc = node.kwargs?.accessibility;
    if (typeof acc !== 'string' || !/^public\b/.test(acc)) return;
    ctx.warnAst('public-section', node,
        '`public section` is not used in `Theorem/`: declare `@[path] theorem main` at the top level instead',
        1, null, null, { col: 1 });
}

/**
 * Number of distinct `lemma` / `theorem` declarations in the tree. `lintLean` compares it with the text scan
 * (`ctx.decls`) and leaves `decl-keyword-dir` to the text fallback when they disagree (a mis-parse).
 */
export function countLemmaTheoremNodes(tree) {
    const { Lean_lemma, Lean_theorem } = Lean.classes;
    const seen = new Set();
    for (const n of walk(tree)) if (n instanceof Lean_lemma || n instanceof Lean_theorem) seen.add(n);
    return seen.size;
}

export function astRules(ctx, tree) {
    const { LeanStatements, LeanArgsNewLineSeparated, Lean_lemma, Lean_theorem, Lean_def, Lean_let, Lean_section } = Lean.classes;
    // findings are emitted in source order (pre-order index of the quoted node) so that `ctx.warnAst` can locate
    // each statement with a forward-moving cursor
    const order = new Map();
    const found = [];
    const lemmaFile = ctx.astCovered.has('decl-keyword-dir') && isLemmaPath(ctx.file);
    const inTheorem = /(^|\/)Theorem\//.test(String(ctx.file ?? '').replace(/\\/g, '/'));
    // `quoteAs`: text to quote instead of the node's own reprint (the node still fixes the source order)
    const sink = { warnAst: (rule, node, msg, maxLines, follow, quoteAs, extra, sequential = false) => found.push({ rule, node, msg, maxLines, follow, quoteAs, extra, sequential }) };
    for (const node of walk(tree)) {
        order.set(node, order.size);
        if (node instanceof Lean_lemma || node instanceof Lean_theorem || node instanceof Lean_def) found.push({ anchor: declName(node), node });
        if (node instanceof Lean_theorem && lemmaFile) declKeywordDir(ctx, node);
        if (node instanceof Lean_lemma || node instanceof Lean_theorem) {
            const bs = givenBinders(node);
            givenImplicitDep(sink, node, bs);
            // one finding per lemma: the consecutive check only when no independent proposition can simply move up
            if (!givenPropFirst(sink, node, bs)) givenPropConsecutive(sink, node, bs);
            // comparisons are style, so only the signature (given hypotheses + conclusion) is checked; proof
            // bodies (`have`, `show`, `rw`, `simp`, `exact`, …) may legitimately compare against a literal
            for (const signatureNode of walk(node.assignment?.lhs)) literalLeftComparison(sink, signatureNode);
            dotNotation(sink, node);
            finGetElemApp(ctx, sink, node);
        }
        else if (node instanceof LeanStatements || node instanceof LeanArgsNewLineSeparated) haveInlineOnce(sink, node);
        else if (node instanceof Lean_let) {
            instanceVariant(sink, node);
            calcAfterAssign(sink, node);
            haveUnderscore(sink, node);
        }
        else if (node instanceof Lean_section) publicSection(sink, node, inTheorem);
        else {
            parenGetElem(sink, node);
            finIndexVal(sink, node);
            parenAppArg(sink, node);
            parenRedundantType(sink, node);
            parenRedundantSumSub(sink, node);
            parenRedundantPow(sink, node);
            parenRedundantBinder(sink, node);
            parenRedundantArith(sink, node);
            parenRedundantAscription(sink, node);
            preferUnicodeType(sink, node);
            preferUnicodePow(sink, node);
            rangeBinder(sink, node);
        }
    }
    found.sort((a, b) => order.get(a.node) - order.get(b.node));
    // Identical reprints (`Fin.ropeEven t` at lines 13 and 17) need their own lines: the
    // n-th `sequential` finding with a given text lands on the n-th exact source occurrence.
    // Search the comment-blanked source so a mention inside a `/-- … -/` doc string does not
    // steal the line from the actual application (e.g. `Fin.castAdd d t` documented then used).
    const seqState = new Map();
    for (const f of found) {
        if (f.sequential) {
            const text = f.quoteAs ?? quote(f.node, 120, 1);
            // `compile` stamps the node with its source line; the text search below is only
            // needed for a synthetic quote with no source node.
            if (f.node?.line != null) {
                ctx.astCursor = f.node.line - 1;
                ctx.warn(f.rule, f.node.line, null, f.msg, { stmt: text });
                continue;
            }
            const key = collapse(text.split('\n')[0]);
            // resume at the character offset just past the previous hit, so a repeated reprint on the
            // same line still finds its own occurrence (`Fin.ropeEven t = Fin.ropeEven t`)
            const state = seqState.get(text) ?? { from: 0, offset: 0, lastLine: null };
            let line = null;
            for (let i = state.from; i < ctx.P.code.length; i++) {
                const hay = collapse(ctx.P.code[i]);
                const at = hay.indexOf(key, i === state.from ? state.offset : 0);
                if (at < 0) continue;
                line = i + 1;
                state.from = i;
                state.offset = at + key.length;
                break;
            }
            // reprint no longer locatable: stay on the previous hit's line rather than emitting `null`
            if (line == null) line = state.lastLine;
            else state.lastLine = line;
            seqState.set(text, state);
            if (line != null) ctx.astCursor = line - 1;
            ctx.warn(f.rule, line, null, f.msg, { stmt: text });
            continue;
        }
        if (!('anchor' in f)) ctx.warnAst(f.rule, f.quoteAs != null ? { toString: () => f.quoteAs } : f.node, f.msg, f.maxLines, f.follow, f.extra);
        else {
            // a declaration: restart the search at its line (from the text scanner) so repeated binders resolve per lemma
            const d = ctx.decls.find((x) => x.name === f.anchor && x.line >= ctx.astCursor);
            if (d) ctx.astCursor = d.line;
        }
    }
}

/**
 * Line of a quoted statement: the first source line at or after `from` (0-based) whose whitespace-free text
 * contains the statement's whitespace-free first line. Returns a 1-based line or null.
 */
export function locate(raw, stmt, from = 0, follow = null) {
    const first = collapse(stmt.split('\n')[0].replace(/…$/, ''));
    if (!first) return null;
    const lines = raw.map(collapse);
    if (follow) {
        // the statement whose next statement (`follow`, first line) starts within its reprinted span (+2 lines)
        const next = collapse(follow.split('\n')[0].replace(/…$/, '')).slice(0, 40);
        const span = String(stmt).split('\n').length + 2;
        for (let i = Math.max(0, from); i < lines.length; i++) {
            if (!lines[i].includes(first.slice(0, 40))) continue;
            for (let k = i + 1; k <= i + span && k < lines.length; k++) if (lines[k].includes(next)) return i + 1;
        }
    }
    // the reprint can differ from the source (`fun x =>` vs `↦`, spacing): fall back to shorter prefixes
    for (const n of [first.length, 40, 24, 12]) {
        if (n > first.length || (n < first.length && n < 8)) continue;
        const key = first.slice(0, n);
        for (let i = Math.max(0, from); i < lines.length; i++) if (lines[i].includes(key)) return i + 1;
    }
    return null;
}
