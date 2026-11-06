/**
 * Logic / boolean connectives: `LeanLogic` and `&&` / `||` / `^^` / `∨` / `∧`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinaryBoolean } from './boolean.js';
import { Lean } from './base.js';
import { pathAndInfixChoices } from './pathChoices.js';
import { strStmt } from './utility.js';

const L = Lean.classes;

export class LeanLogic extends LeanBinaryBoolean {
    static { this.register(); }

    /** @type {boolean|undefined} */
    hanging_indentation;

    is_indented() {
        return this.parent instanceof L.LeanStatements;
    }

    sep() {
        if (this.hanging_indentation) {
            const indent = this.rhs.indent ?? 0;
            return '\n' + ' '.repeat(indent);
        }
        return ' ';
    }

    strFormat() {
        const sep = this.sep();
        return `%s ${this.operator}${sep}%s`;
    }
}

export class LeanLogicAnd extends LeanLogic {
    static { this.register(); }

    static input_priority = 37;

    get stack_priority() {
        return 50;
    }

    get command() {
        return '\\&\\&';
    }

    get operator() {
        return '&&';
    }

    toJSON() {
        const lhs = this.lhs.toJSON();
        const rhs = this.rhs.toJSON();
        const f = this.func;
        const rec = lhs && typeof lhs === 'object' ? lhs : null;
        if (this.lhs instanceof LeanLogicAnd && rec && Array.isArray(rec[f])) {
            return { [f]: [.../** @type {unknown[]} */ (rec[f]), rhs] };
        }
        return { [f]: [lhs, rhs] };
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}

export class LeanLogicOr extends LeanLogic {
    static { this.register(); }

    static input_priority = 37;

    get stack_priority() {
        return 36;
    }

    get command() {
        return '\\|\\|';
    }

    get operator() {
        return '||';
    }

    toJSON() {
        const lhs = this.lhs.toJSON();
        const rhs = this.rhs.toJSON();
        const f = this.func;
        const rec = lhs && typeof lhs === 'object' ? lhs : null;
        if (this.lhs instanceof LeanLogicOr && rec && Array.isArray(rec[f])) {
            return { [f]: [.../** @type {unknown[]} */ (rec[f]), rhs] };
        }
        return { [f]: [lhs, rhs] };
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}

export class LeanLogicXor extends LeanLogic {
    static { this.register(); }

    static input_priority = 33;

    get command() {
        return '\\^\\^';
    }

    get operator() {
        return '^^';
    }

    strFormat() {
        return `%s ${this.operator} %s`;
    }
}

export class Lean_lor extends LeanLogic {
    static { this.register(); }

    static input_priority = 30;

    get stack_priority() {
        return 29;
    }

    get operator() {
        return '∨';
    }

    insert_newline(caret, newline_count, indent, next) {
        if (caret === this.rhs && caret instanceof L.LeanCaret) {
            if (indent >= this.indent) {
                if (indent === this.indent) indent = this.indent + 2;
                this.hanging_indentation = true;
                caret.indent = indent;
                return caret;
            }
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    toJSON() {
        return { [this.func]: [this.lhs.toJSON(), this.rhs.toJSON()] };
    }
}


/**
 * Display-only: flatten nested `∧` of plain `=` into an eq chain when sides connect
 * (`a = b ∧ b = c ∧ c = d` → `a = b = c = d`), matching py `And._latex` + `connected_equations`.
 * Does not change Lean syntax / strFormat.
 * @param {InstanceType<typeof L.Lean_land>} land
 * @returns {object[] | null} ordered side nodes, or null if not a pure connected eq chain
 */
function eqChainSides(land) {
    /** @param {object} n */
    function flatten(n) {
        while (n instanceof L.LeanParenthesis) n = n.arg;
        if (n instanceof L.Lean_land) return [...flatten(n.lhs), ...flatten(n.rhs)];
        return [n];
    }
    const parts = flatten(land);
    if (parts.length < 2) return null;
    const pairs = [];
    for (const p of parts) {
        let n = p;
        while (n instanceof L.LeanParenthesis) n = n.arg;
        // Plain `=` only (no =ᵐ / =ᶠ superscripts).
        if (!(n instanceof L.LeanEq) || n.superscript) return null;
        let [lhs, rhs] = [n.lhs, n.rhs];
        while (lhs instanceof L.LeanParenthesis) lhs = lhs.arg;
        while (rhs instanceof L.LeanParenthesis) rhs = rhs.arg;
        pairs.push([lhs, rhs]);
    }
    // Same algorithm as py sympy.logic.boolalg.And.connected_equations
    const child = new Map();
    const parent = new Map();
    let lastLhs = null;
    for (const [lhs, rhs] of pairs) {
        const lk = strStmt(lhs);
        const rk = strStmt(rhs);
        if (child.has(lk)) return null;
        child.set(lk, { node: rhs, key: rk });
        if (parent.has(rk)) return null;
        parent.set(rk, { node: lhs, key: lk });
        lastLhs = { node: lhs, key: lk };
    }
    if (!lastLhs) return null;
    let root = lastLhs;
    while (parent.has(root.key)) root = parent.get(root.key);
    const children = [root.node];
    let nextKey = root.key;
    while (child.has(nextKey)) {
        const step = child.get(nextKey);
        children.push(step.node);
        nextKey = step.key;
    }
    if (children.length !== pairs.length + 1) return null;
    return children;
}

export class Lean_land extends LeanLogic {
    static { this.register(); }

    static input_priority = 35;

    get stack_priority() {
        return 34;
    }

    get operator() {
        return '∧';
    }

    /**
     * Display latex: collapse connected plain-eq ∧-chains (py And._latex).
     * @param {object} [syntax]
     * @returns {string}
     */
    toLatex(syntax) {
        const sides = eqChainSides(this);
        if (sides) return sides.map((s) => `{${s.toLatex(syntax)}}`).join(' = ');
        return super.toLatex(syntax);
    }

    /**
     * And as a binary operator (like Eq): `LHS/and/RHS` and `And(LHS)(RHS)`.
     * Each argument's pathChoices supplies the side list (`""` = omit). Both omit → `And__`.
     * @param {object} [opts]
     * @returns {string[]}
     */
    pathChoices(opts = {}) {
        return pathAndInfixChoices(
            this.lhs?.pathChoices?.(opts) ?? [""],
            this.rhs?.pathChoices?.(opts) ?? [""],
        ).stems;
    }

    insert_newline(caret, newline_count, indent, next) {
        if (caret === this.rhs && caret instanceof L.LeanCaret) {
            if (indent >= this.indent) {
                this.hanging_indentation = true;
                caret.indent = indent;
                return caret;
            }
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    toJSON() {
        return { [this.func]: [this.lhs.toJSON(), this.rhs.toJSON()] };
    }
}
