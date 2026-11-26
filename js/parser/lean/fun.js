/**
 * Lambda binder head: `Lean_fun` (`fun` / `λ`).
 *
 * `args` is heterogeneous, discriminated by kind:
 *   simple lambda: `[<arrow node>]`
 *   match lambda:  `[LeanBar, LeanBar, …]` (`fun | p => e | q => e`)
 * Use `is_match_lambda` rather than `args.length` (a one-arm match lambda has length 1).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanArgs } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

/**
 * Collect plain identifier names from a binder tree.
 * Skips non-simple names like `«\sf{a}»`, `c✝`, exactly as `LeanToken.is_variable()` does.
 */
function collectBinderNames(node, out = []) {
    if (!node) return out;
    if (node instanceof L.LeanToken) {
        if (node.is_variable() && node.text !== '') out.push(node.text);
    } else if (node instanceof L.LeanColon) {
        collectBinderNames(node.lhs, out);
    } else if (node instanceof L.LeanParenthesis) {
        collectBinderNames(node.arg, out);
    } else if (node instanceof L.LeanArgsSpaceSeparated) {
        for (const a of node.args) collectBinderNames(a, out);
    }
    return out;
}

/** `fun` (λ-style binder head). */
export class Lean_fun extends LeanArgs {
    static { this.register(); }

    static input_priority = 18;

    /**
     * @param {Lean} arg arrow node, or the still-empty caret right after `fun`
     * @param {number} indent
     * @param {number} level
     * @param {import('../node.js').Node | null} [parent]
     */
    constructor(arg, indent, level, parent = null) {
        super([arg], indent, level, parent);
    }

    get operator() {
        return 'fun';
    }
    get command() {
        return '\\lambda';
    }

    /** Match lambda (`fun | p => e | q => e`): every arg is a `LeanBar`. */
    get is_match_lambda() {
        return this.args[0] instanceof L.LeanBar;
    }

    /** Compatibility alias for the simple-lambda body. */
    get arg() {
        return this.args[0];
    }
    set arg(v) {
        this.args[0] = v;
        if (v) v.parent = this;
    }

    is_indented() {
        const parent = this.parent;
        return parent instanceof L.LeanArgsNewLineSeparated || parent instanceof L.LeanStatements;
    }

    /** Plain identifier names bound by this lambda (one scope per arm for match lambdas). */
    binderNames() {
        if (this.is_match_lambda) {
            const names = this.args.flatMap((bar) => collectBinderNames(bar?.arg?.lhs));
            return [...new Set(names)];
        }
        return collectBinderNames(this.arg?.lhs);
    }

    /**
     * Lambda introduces binders; `ctx.binders` gets the plain names pushed before
     * serializing the RHS so bound tokens render as De Bruijn `?0`, `?1`, …
     * Exactly mirrors `LeanBigOperator.pushBinderNames`. Match lambdas push each
     * bar's own names only for that bar.
     */
    toJSON(ctx = { leaves: new Map() }) {
        ctx.binders ??= [];
        const depth = ctx.binders.length;
        try {
            if (this.is_match_lambda) {
                const arms = [];
                for (const bar of this.args) {
                    const arrow = bar?.arg;
                    const d = ctx.binders.length;
                    try {
                        ctx.binders.push(...collectBinderNames(arrow?.lhs));
                        if (arrow && typeof arrow === 'object' && 'lhs' in arrow && 'rhs' in arrow) {
                            arms.push([arrow.lhs.toJSON(ctx), arrow.rhs.toJSON(ctx)]);
                        } else {
                            arms.push(bar.toJSON(ctx));
                        }
                    } finally {
                        ctx.binders.length = d;
                    }
                }
                return { [this.pathToken]: arms };
            }
            ctx.binders.push(...this.binderNames());
            const arrow = this.arg;
            if (arrow && typeof arrow === 'object' && 'lhs' in arrow && 'rhs' in arrow) {
                return { [this.pathToken]: [arrow.lhs.toJSON(ctx), arrow.rhs.toJSON(ctx)] };
            }
            return { [this.pathToken]: arrow ? arrow.toJSON(ctx) : '' };
        } finally {
            ctx.binders.length = depth;
        }
    }

    /**
     * `fun` followed by a newline and a `|`: the arms belong to this lambda,
     * so keep the caret inside instead of ending the lambda.
     */
    insert_newline(caret, newline_count, indent, next) {
        if (next === '|' && caret === this.args[0] && caret instanceof L.LeanCaret) {
            caret.indent = indent;
            this.armIndent = indent;
            this.pendingArmNewlines = newline_count;
            return caret;
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    /** `|` under a match lambda: make the pending caret a new arm (`LeanBar`). */
    insert_bar(caret, prevToken, next) {
        const last = this.args[this.args.length - 1];
        if (last === caret && caret instanceof L.LeanCaret) {
            const bar = new L.LeanBar(caret, caret.indent, caret.level);
            bar.newlineCount = this.pendingArmNewlines ?? 0;
            delete this.pendingArmNewlines;
            this.args[this.args.length - 1] = bar;
            bar.parent = this;
            return caret;
        }
        return super.insert_bar(caret, prevToken, next);
    }

    /**
     * Newline before another `|` arm: find the match lambda owning this indent and
     * append a blank arm slot. Mirrors `LeanWith.findAlternativeCaret`.
     */
    static findAlternativeCaret(node, indent, newline_count = 1) {
        for (let p = node; p; p = p.parent) {
            if (p instanceof Lean_fun) {
                if (p.armIndent !== indent) return null;
                const last = p.args[p.args.length - 1];
                if (last instanceof L.LeanBar) {
                    const caret = new L.LeanCaret(indent, last.level);
                    p.pendingArmNewlines = newline_count;
                    p.push(caret);
                    return caret;
                }
                return null;
            }
            if (p instanceof L.LeanStatements || p instanceof L.LeanModule) break;
        }
        return null;
    }

    /**
     * Nearest enclosing match lambda whose arm body contains `node`.
     * Stops at grouping/other binder nodes so `{x | …}`, `μ[x | s]`, nested
     * matches and tactics keep their own `|` handling.
     */
    static enclosingMatchLambda(node) {
        const stop = [
            L.LeanParenthesis, L.LeanBrace, L.LeanBracket, L.LeanGet, L.LeanIte,
            L.Lean_match, L.LeanWith, L.LeanBigOperator, L.LeanTactic,
            L.LeanStatements, L.LeanModule,
        ];
        for (let p = node?.parent; p; p = p.parent) {
            if (p instanceof Lean_fun) return p.is_match_lambda ? p : null;
            if (stop.some((C) => C && p instanceof C)) return null;
        }
        return null;
    }

    /** Append one more arm (`|` inline, e.g. `fun | p => e | q => e`). */
    appendArm(node) {
        const indent = this.armIndent ?? this.indent;
        const caret = new L.LeanCaret(indent, node?.level ?? this.level);
        const bar = new L.LeanBar(caret, indent, caret.level);
        bar.newlineCount = 0;
        this.push(bar);
        return caret;
    }

    latexFormat() {
        if (this.is_match_lambda) {
            const cases = Array(this.args.length).fill('%s').join(' \\\\ ');
            return `${this.command}\\ \\begin{cases} ${cases} \\end{cases}`;
        }
        return `${this.command}\\ %s`;
    }
    strFormat() {
        if (!this.is_match_lambda) return `${this.operator} %s`;
        let s = this.operator;
        for (const bar of this.args) {
            const n = bar?.newlineCount ?? 0;
            s += (n > 0 ? '\n'.repeat(n) : ' ') + '%s';
        }
        return s;
    }
}
