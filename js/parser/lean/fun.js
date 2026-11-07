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
    toJSON() {
        return { [this.operator]: this.arg.toJSON() };
    }

    /** `fun k => f k i` is one ternary `Ext`, not a nested `Fun`. */
    storedHoleRegex(opts, binders) {
        if (typeof opts.isHole !== "function" || typeof opts.decomp !== "function" || typeof opts.peel !== "function")
            return null;
        let body = this.args?.length > 1 ? this.args[this.args.length - 1] : (this.arg ?? this.args?.[0]);
        body = opts.peel(body);
        const nameOf = (n) => n?.constructor?.name || "";
        if (nameOf(body) === "LeanRightarrow" || nameOf(body) === "Lean_mapsto") {
            const b = body.args?.[0];
            if (nameOf(b) === "LeanToken" && b.text && b.text !== "_") binders.add(b.text);
            body = opts.peel(body.args?.[1]);
        } else if (nameOf(this.args?.[0]) === "LeanToken" && this.args[0].text && this.args[0].text !== "_") {
            binders.add(this.args[0].text);
        }
        const app = opts.peel(body);
        if (nameOf(app) !== "LeanArgsSpaceSeparated") return null;
        const args = app.args || [];
        if (args.length < 2) return null;
        let s = "Ext";
        for (const a of args) {
            if (opts.isHole(a, opts, binders)) s += "_";
            else {
                const d = opts.decomp(a, binders);
                if (!d) return null;
                s += "(" + d + ")";
            }
        }
        return s;
    }
    latexFormat() {
        return `${this.command}\\ %s`;
    }
    strFormat() {
        return `${this.operator} %s`;
    }
}
