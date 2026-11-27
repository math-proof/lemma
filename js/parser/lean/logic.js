/**
 * Logic / boolean connectives: `LeanLogic` and `&&` / `||` / `^^` / `∨` / `∧`.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanBinaryBoolean } from './boolean.js';
import { Lean } from './base.js';
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
        if (typeof this.opLeadIndent === 'number') return ' ';
        if (this.hanging_indentation) {
            const indent = this.rhs.indent ?? 0;
            return '\n' + ' '.repeat(indent);
        }
        return ' ';
    }

    strFormat() {
        if (typeof this.opLeadIndent === 'number') return this.opJoin(this.operator);
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

    toJSON(ctx = { leaves: new Map() }) {
        const lhs = this.lhs.toJSON(ctx);
        const rhs = this.rhs.toJSON(ctx);
        const f = this.pathToken;
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

    toJSON(ctx = { leaves: new Map() }) {
        const lhs = this.lhs.toJSON(ctx);
        const rhs = this.rhs.toJSON(ctx);
        const f = this.pathToken;
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

    static isRightAssociative = true;

    get stack_priority() {
        return 29;
    }

    get operator() {
        return '∨';
    }

    get pathToken() {
        return "Or";
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

    static isRightAssociative = true;

    get stack_priority() {
        return 34;
    }

    get operator() {
        return '∧';
    }

    get pathToken() {
        return "And";
    }

    /**
     * The `ℙ[…]` whose event this `∧` is, if the parent is one (the `(…)` that
     * delimits the probability scope is transparent).
     * @returns {object|null}
     */
    probEventParent() {
        let p = this.parent;
        while (p instanceof L.LeanParenthesis) p = p.parent;
        return p instanceof L.Lean_Prob ? p : null;
    }

    /**
     * Inside a `ℙ[…]` event the conjunction is a joint observation:
     * `ℙ[π](x[:k] = «\sf{x}»[:k] ∧ y[:k] = «\sf{y}»[:k])` stores the joint
     * random vector as `{"Joint": [«\sf{x}»[:k], «\sf{y}»[:k]]}` — only the
     * right-hand sides of the conjoined equalities are fingerprinted.
     * @param {{leaves: Map<string, number>, binders: string[]}} [ctx]
     */
    toJSON(ctx = { leaves: new Map() }) {
        if (!this.probEventParent()) return super.toJSON(ctx);
        const parts = [];
        const push = (node) => {
            let n = node;
            while (n instanceof L.LeanParenthesis) n = n.arg;
            if (n instanceof Lean_land) {
                push(n.lhs);
                push(n.rhs);
                return;
            }
            parts.push((n instanceof L.LeanEq ? n.rhs : n).toJSON(ctx));
        };
        push(this.lhs);
        push(this.rhs);
        return { Joint: parts };
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
}
