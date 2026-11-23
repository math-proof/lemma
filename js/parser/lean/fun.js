/**
 * Lambda binder head: `Lean_fun` (`fun` / `λ`).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanUnary } from './abstract.js';
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
export class Lean_fun extends LeanUnary {
    static { this.register(); }

    static input_priority = 18;
    get operator() {
        return 'fun';
    }
    get command() {
        return '\\lambda';
    }
    is_indented() {
        const parent = this.parent;
        return parent instanceof L.LeanArgsNewLineSeparated || parent instanceof L.LeanStatements;
    }

    /** Plain identifier names bound by this lambda. */
    binderNames() {
        const rhs = this.arg;
        const lhs = rhs?.lhs;
        return collectBinderNames(lhs);
    }

    /**
     * Lambda introduces binders; `ctx.binders` gets the plain names pushed before
     * serializing the RHS so bound tokens render as De Bruijn `?0`, `?1`, …
     * Exactly mirrors `LeanBigOperator.pushBinderNames`.
     */
    toJSON(ctx = { leaves: new Map() }) {
        ctx.binders ??= [];
        const depth = ctx.binders.length;
        const names = this.binderNames();
        try {
            ctx.binders.push(...names);
            const arrow = this.arg;
            if (arrow && typeof arrow === 'object' && 'lhs' in arrow && 'rhs' in arrow) {
                return { [this.pathToken]: [arrow.lhs.toJSON(ctx), arrow.rhs.toJSON(ctx)] };
            }
            return { [this.pathToken]: arrow.toJSON(ctx) };
        } finally {
            ctx.binders.length = depth;
        }
    }

    latexFormat() {
        return `${this.command}\\ %s`;
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}
