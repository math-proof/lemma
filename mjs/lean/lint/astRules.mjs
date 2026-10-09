/**
 * AST-based lint rules on the lean.js parse tree (`js/parser/lean.js`).
 *
 * The tree has no source positions, so these warnings quote the offending statement (`String(node)`, the tree's own
 * reprint of the code) in `stmt`; `line` is filled in when the quoted first line can be found in the source.
 * A parse failure disables the AST rules silently and the text-scan fallbacks run instead (see `AST_RULES`).
 */
import '../../../js/py.js';
import { compile, Lean, LeanModule } from '../../../js/parser/lean.js';

/** rule ids implemented here; their text-scan versions only run when the AST is unavailable */
export const AST_RULES = new Set(['have-inline-once', 'given-prop-first', 'given-prop-consecutive', 'tactic-haveI', 'tactic-letI', 'calc-after-assign', 'decl-keyword-dir']);

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
    const { Lean_have, Lean_replace, LeanAssign, LeanColon, LeanToken, LeanTactic, LeanAt, Lean_let, Lean_set } = Lean.classes;
    const args = stmts.args;
    for (let i = 0; i < args.length; i++) {
        const st = args[i];
        if (!(st instanceof Lean_have) || st instanceof Lean_replace || st.args.length !== 1) continue;
        const assign = st.args[0];
        if (!(assign instanceof LeanAssign)) continue;
        let lhs = assign.lhs;
        if (lhs instanceof LeanColon) lhs = lhs.lhs;
        if (!(lhs instanceof LeanToken) || !lhs.text || lhs.text === 'this') continue;
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

/** does `node` mention `name` free (not re-bound by `∀ name, …` / `∑ name ∈ s, …` / `fun name => …`)? */
function mentions(node, name) {
    const { LeanToken, LeanBigOperator, Lean_fun, LeanRightarrow } = Lean.classes;
    if (!node || typeof node !== 'object') return false;
    if (node instanceof LeanToken) return node.text === name;
    let scope = null;
    if (node instanceof LeanBigOperator && node.args?.length === 2) scope = [node.args[0], node.args[1]];
    else if (node instanceof Lean_fun && node.arg instanceof LeanRightarrow) scope = [node.arg.lhs, node.arg.rhs];
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

/** is the repo-relative path a `Lemma/…` file? */
export function isLemmaPath(file) {
    return /(^|\/)Lemma\//.test(String(file ?? '').replace(/\\/g, '/'));
}

/**
 * `decl-keyword-dir`: a `theorem` in a `Lemma/` file (AGENTS.md: `Lemma/` holds only `lemma`s). The keyword is the
 * node class (`Lean_theorem`), so modifiers (`private`, `noncomputable`, `@[…]`), comments, strings and names like
 * `theorem_foo` never match. Quotes the declaration head (the reprint's line holding the keyword).
 * (`sympy/` files are never rendered or linted, so the `lemma`-in-`sympy/` half is not checked.)
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
    // located on its own (not with the shared forward cursor): a mis-parsed `@[…]` can nest one declaration in the
    // next, so tree order need not be source order; repeated heads take the next unused matching line
    ctx.declHeadLines ??= new Set();
    const first = locate(ctx.P.raw, stmt, 0);
    let line = first;
    while (line != null && ctx.declHeadLines.has(line)) line = locate(ctx.P.raw, stmt, line);
    // every matching source line already reported: the parser produced this declaration twice (mis-nesting)
    if (first != null && line == null) return;
    if (line != null) ctx.declHeadLines.add(line);
    ctx.warn('decl-keyword-dir', line, null, `\`theorem${name ? ` ${name}` : ''}\` in \`Lemma/\`: declare it with \`lemma\``, { stmt });
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
    const { LeanStatements, LeanArgsNewLineSeparated, Lean_lemma, Lean_theorem, Lean_def, Lean_let } = Lean.classes;
    // findings are emitted in source order (pre-order index of the quoted node) so that `ctx.warnAst` can locate
    // each statement with a forward-moving cursor
    const order = new Map();
    const found = [];
    const lemmaFile = ctx.astCovered.has('decl-keyword-dir') && isLemmaPath(ctx.file);
    // `quoteAs`: text to quote instead of the node's own reprint (the node still fixes the source order)
    const sink = { warnAst: (rule, node, msg, maxLines, follow, quoteAs) => found.push({ rule, node, msg, maxLines, follow, quoteAs }) };
    for (const node of walk(tree)) {
        order.set(node, order.size);
        if (node instanceof Lean_lemma || node instanceof Lean_theorem || node instanceof Lean_def) found.push({ anchor: declName(node), node });
        if (node instanceof Lean_theorem && lemmaFile) declKeywordDir(ctx, node);
        if (node instanceof Lean_lemma || node instanceof Lean_theorem) {
            const bs = givenBinders(node);
            // one finding per lemma: the consecutive check only when no independent proposition can simply move up
            if (!givenPropFirst(sink, node, bs)) givenPropConsecutive(sink, node, bs);
        }
        else if (node instanceof LeanStatements || node instanceof LeanArgsNewLineSeparated) haveInlineOnce(sink, node);
        else if (node instanceof Lean_let) {
            instanceVariant(sink, node);
            calcAfterAssign(sink, node);
        }
    }
    found.sort((a, b) => order.get(a.node) - order.get(b.node));
    for (const f of found) {
        if (!('anchor' in f)) ctx.warnAst(f.rule, f.quoteAs != null ? { toString: () => f.quoteAs } : f.node, f.msg, f.maxLines, f.follow);
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
