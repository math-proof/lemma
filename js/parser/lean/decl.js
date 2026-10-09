/**
 * Declarations and binders: `Lean_def`, `theorem` / `abbrev` / `lemma`,
 * `let` / `have` / `set` / `replace` / `show`. JS also has `where`, `class`,
 * `instance`, `macro`, and `syntax` in this cluster; PHP does not.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanArgs, LeanBinary } from './abstract.js';
import { LeanSyntax } from './tactic.js';
import { Lean } from './base.js';

const L = Lean.classes;

export class Lean_def extends LeanArgs {
    static { this.register(); }

    get stack_priority() {
        return 7;
    }

    get operator() {
        return 'def';
    }

    /**
     * @param {string|Lean} accessibility
     * @param {Lean|number} name
     * @param {number} [indent]
     * @param {number} [level]
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(accessibility, name, indent, level, parent = null) {
        if (level === null || level === undefined) {
            indent = name;
            name = accessibility;
            accessibility = 'public';
            level = name instanceof L.Lean ? name.level : 0;
        }
        super([name], indent, level, parent);
        this.args.unshift(null);
        this.kwargs.accessibility = accessibility;
    }

    get accessibility() {
        return this.kwargs.accessibility;
    }

    set accessibility(v) {
        this.kwargs.accessibility = v;
    }

    get attribute() {
        return this.args[0];
    }

    set attribute(v) {
        this.args[0] = v;
        if (v) v.parent = this;
    }

    get assignment() {
        return this.args[1];
    }

    set assignment(v) {
        this.args[1] = v;
        if (v) v.parent = this;
    }

    strArgs() {
        const [attr, assignment] = this.args;
        if (attr == null) return [assignment];
        return this.args;
    }

    strFormat() {
        const acc = this.accessibility === 'public' ? '' : `${this.accessibility} `;
        let def = `${acc}${this.func} %s`;
        if (this.attribute) def = `%s\n${def}`;
        return def;
    }

    latexFormat() {
        return this.strFormat();
    }

    toJSON() {
        const json = {
            [this.operator]: super.toJSON(),
            accessibility: this.accessibility,
        };
        if (this.attribute) json.attribute = this.attribute.toJSON();
        return json;
    }

    insert_tactic(caret, token) {
        return this.insert_word(caret, token);
    }

    is_indented() {
        return false;
    }

    set_line(line) {
        this.line = line;
        let lineNo = line;
        const attr = this.attribute;
        if (attr) lineNo = attr.set_line(lineNo) + 1;
        return this.assignment.set_line(lineNo);
    }

    relocate_last_comment() {
        const assignment = this.assignment;
        if (assignment instanceof L.LeanAssign) assignment.relocate_last_comment();
    }

    /**
     * Port of `Lean_def::insert_newline`.
     * Stops indented proof lines from bubbling to `LeanModule` (which would throw).
     */
    insert_newline(caret, newline_count, indent, next) {
        if (this.indent < indent) {
            if (caret === this.assignment) {
                const $new = this.push_args_indented(indent, newline_count);
                if ($new) return $new;
                if (caret instanceof L.LeanColon) {
                    if (caret.rhs instanceof L.LeanCaret) {
                        caret = caret.rhs;
                        caret.indent = indent;
                        this.assignment.rhs = new L.LeanStatements([caret], indent, caret.level);
                        return caret;
                    }
                } else if (caret instanceof L.LeanAssign) {
                    const {rhs} = this.assignment;
                    if (rhs instanceof L.LeanCaret) {
                        rhs.indent = indent;
                        this.assignment.rhs = new L.LeanStatements([rhs], indent, rhs.level);
                        return rhs;
                    }
                    if (rhs instanceof L.LeanArgsNewLineSeparated || rhs instanceof L.LeanStatements) {
                        const c = new L.LeanCaret(indent, rhs.level);
                        rhs.push(c);
                        return c;
                    }
                }
            }
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }
}

export class Lean_theorem extends Lean_def {
    static { this.register(); }
}

export class Lean_abbrev extends Lean_def {
    static { this.register(); }
}

export class Lean_where extends LeanBinary {
    static { this.register(); }

    static input_priority = 18;

    get operator() {
        return 'where';
    }

    get command() {
        return 'where';
    }

    sep() {
        return this.rhs instanceof L.LeanCaret ? ' ' : '\n';
    }

    /**
     * Capture the indented field block after `where` (mirrors `Lean_def::insert_newline`
     * wrapping the `:=` rhs into a `LeanStatements`).
     */
    insert_newline(caret, newline_count, indent, next) {
        if (this.indent < indent && caret === this.rhs && this.rhs instanceof L.LeanCaret) {
            const rhs = this.rhs;
            rhs.indent = indent;
            this.rhs = new L.LeanStatements([rhs], indent, rhs.level);
            return rhs;
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }
}

export class Lean_class extends Lean_def {
    static { this.register(); }
}

export class Lean_instance extends Lean_def {
    static { this.register(); }
}

export class Lean_macro extends Lean_def {
    static { this.register(); }
}

export class Lean_syntax extends Lean_def {
    static { this.register(); }
}

export class Lean_lemma extends Lean_def {
    static { this.register(); }

    echo() {
        this.assignment.echo();
        const asn = this.assignment;
        if (asn instanceof L.LeanAssign && asn.rhs instanceof L.LeanBy) {
            const statement = asn.rhs.arg;
            if (statement instanceof L.LeanStatements) {
                const stmts = statement.args;
                for (let i = stmts.length - 1; i >= 0; i--) {
                    const stmt = stmts[i];
                    if (stmt.is_comment()) continue;
                    if (stmt instanceof L.LeanTactic || stmt instanceof Lean_let) {
                        const token = stmt.get_echo_token();
                        // try echo ⊢
                        if (token) {
                            const {indent, level} = statement;
                            statement.push(
                                new L.LeanTactic(
                                    'try',
                                    new L.LeanTactic('echo', token, indent, level),
                                    indent,
                                    level,
                                ),
                            );
                        }
                        break;
                    }
                }
            }
        }
    }
}

// binding tactic
export class Lean_let extends LeanSyntax {
    static { this.register(); }

    static input_priority = 7;

    /**
     * @param {Lean} arg
     * @param {number} indent
     * @param {number} level
     * @param {import('./node.js').Node | null} [parent]
     */
    constructor(arg, indent, level, parent = null) {
        super([arg], indent, level, parent);
    }

    get command() {
        return 'let';
    }

    /**
     * Source keyword: `operator`, or its instance variant (`letI` / `haveI`) when the node was parsed from one.
     * `inst` is set by the parser (`base.js`, case 'haveI' / 'letI'); the tree shape is the same as `let` / `have`.
     */
    get keyword() {
        return this.inst ? `${this.operator}I` : this.operator;
    }

    /**
     * Find the first nested by tactic block under a term proof RHS
     * (e.g. funext fun om |-> by ...). Used by echo() and split().
     */
    static findNestedByStatements(node, seen = new Set()) {
        if (!node || typeof node !== 'object' || seen.has(node)) return null;
        seen.add(node);
        if (node instanceof L.LeanBy && node.arg instanceof L.LeanStatements) {
            return { by: node, stmts: node.arg };
        }
        if (Array.isArray(node.args)) {
            for (const a of node.args) {
                const found = Lean_let.findNestedByStatements(a, seen);
                if (found) return found;
            }
        }
        return null;
    }

    /**
     * Walk a term proof (e.g. funext fun om |-> by ... / fun _ |-> by ...) and echo nested by / calc bodies.
     * Top-level := by is handled directly in echo(); this covers the same split when by is nested in a term.
     */
    static echoNestedByBodies(node) {
        const nested = Lean_let.findNestedByStatements(node);
        if (nested) {
            nested.stmts.echo();
            return;
        }
        if (!node || typeof node !== 'object') return;
        if (node instanceof L.LeanCalc) {
            node.echo();
            return;
        }
        if (Array.isArray(node.args)) {
            for (const a of node.args) {
                if (a instanceof L.LeanCalc) a.echo();
            }
        }
    }

    echo() {
        const token = this.get_echo_token();
        const proof = this.args[0]?.rhs;
        if (proof instanceof L.LeanBy) {
            const stmt = proof.arg;
            if (stmt instanceof L.LeanStatements) stmt.echo();
        } else if (proof instanceof L.LeanCalc) {
            proof.echo();
        } else if (proof) {
            // have h : T := funext fun om |-> by ... -- RHS is a term, not by; still split the nested tactic block.
            Lean_let.echoNestedByBodies(proof);
        }
        if (token) {
            return [1, this, new L.LeanTactic('echo', token, this.indent, token.level)];
        }
    }

    get_echo_token() {
        const assign = this.args[0];
        if (assign instanceof L.LeanAssign) {
            const lhs = assign.lhs;
            if (lhs instanceof L.LeanAngleBracket) {
                const token = lhs.tokens_comma_separated();
                if (token.length === 1) return token[0];
                return new L.LeanArgsCommaSeparated(token, this.indent, lhs.level);
            }
            if (lhs instanceof L.LeanToken) return lhs;
            if (lhs instanceof L.LeanColon && lhs.lhs instanceof L.LeanToken) return lhs.lhs;
            if (lhs instanceof L.LeanArgsSpaceSeparated && lhs.args[0] instanceof L.LeanToken) return lhs.args[0];
        }
    }

    insert_newline(caret, newline_count, indent, next) {
        if (caret === this.args[0]) {
            if (next === '<' && this.parent instanceof L.LeanSequentialTacticCombinator) {
                const c = new L.LeanCaret(indent, caret.level);
                this.push(c);
                return c;
            }
        }
        return super.insert_newline(caret, newline_count, indent, next);
    }

    /**
     * Term-mode `let x := v; body` (e.g. a binder type `(h : let r := f; P r)`, or the rhs of `:=`):
     * the `;` ends the value and starts the body, which becomes `args[1]` (`this.semicolon` is set).
     * Without this, the `;` bubbles up to the enclosing `( … )` and splits the binder into
     * `LeanArgsSemicolonSeparated`, losing the hypothesis.
     * In tactic position (`LeanStatements`, `by`, `·` blocks…) the `;` still separates tactics.
     */
    insert_semicolon(caret) {
        if (caret === this.args[0] && this.args.length === 1 && this.is_term()) {
            const c = new L.LeanCaret(this.indent, caret.level);
            this.semicolon = true;
            this.push(c);
            return c;
        }
        return super.insert_semicolon(caret);
    }

    /** `(h : let r := f; P r)` is a hypothesis iff its body `P r` is a proposition. */
    isProp(vars) {
        if (this.semicolon && this.args.length === 2) return this.args[1].isProp(vars);
        return super.isProp(vars);
    }

    /** Whether this `let` sits in term position, where `;` introduces the body rather than a new tactic. */
    is_term() {
        const parent = this.parent;
        if (parent instanceof L.LeanColon || parent instanceof L.LeanAssign) return parent.rhs === this;
        if (parent instanceof L.LeanParenthesis) return true;
        if (parent instanceof Lean_let) return parent.semicolon === true && parent.args[1] === this;
        // `(h :⏎    let r := f; P r)`: the newline after `:` wraps the type in `LeanStatements`
        // (the lemma's own `:⏎ let …` conclusion is not affected: its colon is not inside `( … )` / `have`)
        if (parent instanceof L.LeanStatements) {
            const colon = parent.parent;
            return colon instanceof L.LeanColon && colon.rhs === parent &&
                (colon.parent instanceof L.LeanParenthesis || colon.parent instanceof Lean_let);
        }
        return false;
    }

    insert_sequential_tactic_combinator(caret, prevToken, nextToken) {
        const last = this.args[this.args.length - 1];
        if (caret === last) {
            if (caret instanceof L.LeanCaret) {
                this.replace(
                    caret,
                    new L.LeanSequentialTacticCombinator(
                        caret,
                        prevToken == '\n' ? caret.indent : this.indent,
                        caret.level,
                        prevToken == '\n',
                        nextToken == '\n'
                    ),
                );
            } else {
                const c = new L.LeanCaret(0, 0);
                this.push(new L.LeanSequentialTacticCombinator(c, this.indent, c.level, false, true));
            }
            return caret;
        }
        throw new Error(`insert_sequential_tactic_combinator is unexpected for ${this.constructor.name}`);
    }

    is_indented() {
        const parent = this.parent;
        // term-mode `(h : let r := f; P r)`: inline, no leading indentation
        if (parent instanceof L.LeanColon || parent instanceof L.LeanParenthesis || parent instanceof Lean_let)
            if (this.is_term()) return false;
        if (parent instanceof L.LeanSequentialTacticCombinator) return this.indent > 0;
        if (parent instanceof L.LeanTacticBlock) return this.indent > parent.indent;
        return !(parent instanceof L.LeanArgsSemicolonSeparated);
    }

    toJSON() {
        return {
            [this.operator]: this.args[0].toJSON(),
        };
    }

    latexFormat() {
        const head = `{\\color{#00f}${this.command}${this.inst ? 'I' : ''}}\\ `;
        // term-mode `let x := v; body`
        if (this.semicolon && this.args.length === 2) return head + '%s;\\ %s';
        return head + Array(this.args.length).fill('%s').join('\\ ');
    }

    get operator() {
        return 'let';
    }

    split(syntax) {
        const assign = this.args[0];
        if (assign instanceof L.LeanAssign) {
            const proof = assign.rhs;
            if (
                (proof instanceof L.LeanBy && proof.arg instanceof L.LeanStatements) ||
                proof instanceof L.LeanCalc
            ) {
                const statements = assign.split(syntax);
                const Ctor = this.constructor;
                statements[0] = new Ctor(statements[0], this.indent, assign.level);
                if (this.inst) statements[0].inst = true;
                return statements;
            }
            // Term proof with nested by (funext fun om |-> by ...): flatten like := by
            if (proof) {
                const self = this.clone();
                const nested = Lean_let.findNestedByStatements(self.args[0].rhs);
                if (nested) {
                    const stmts = nested.stmts;
                    nested.by.arg = new L.LeanCaret(nested.by.indent, nested.by.level);
                    const statements = [self];
                    stmts.swap_echo_star(syntax, statements);
                    return statements;
                }
            }
        }
        return [this];
    }

    get stack_priority() {
        // term-mode `let x := v; body`: the body extends as far as possible, but a trailing `:=` / `where`
        // (`have h : let x := v; P x := proof`) belongs to the enclosing declaration
        return this.semicolon ? 18 : 7;
    }

    /** `let := v` / `have : T := v`: no name before `:=` / `:` */
    anonymous() {
        const assign = this.args[0];
        if (!(assign instanceof L.LeanAssign)) return false;
        const lhs = assign.lhs;
        return lhs instanceof L.LeanCaret || (lhs instanceof L.LeanColon && lhs.lhs instanceof L.LeanCaret);
    }

    strFormat() {
        const func = this.keyword;
        const parts = [];
        for (const arg of this.args) {
            if (arg instanceof L.LeanCaret);
            else if (this.semicolon && arg === this.args[1]) parts.push('; '); // term-mode `let x := v; body`
            else if (arg === this.args[0] && this.inst && this.anonymous()) parts.push(''); // `letI := inst`
            else if (
                arg instanceof L.LeanSequentialTacticCombinator &&
                (arg.newlineBehind || arg.newlineBefore)
            ) {
                parts.push('\n');
            } else parts.push(' ');
            parts.push('%s');
        }
        return func + parts.join('');
    }
}

export class Lean_have extends Lean_let {
    static { this.register(); }

    get command() {
        return 'have';
    }

    get operator() {
        return 'have';
    }

    get_echo_token() {
        const assign = this.args[0];
        if (!(assign instanceof L.LeanAssign)) return;
        let token = assign.lhs;
        if (token instanceof L.LeanColon)
            token = token.lhs;
        if (token instanceof L.LeanCaret)
            token = new L.LeanToken('this', this.indent, token.level);
        if (token instanceof L.LeanArgsSpaceSeparated && token.args[0] instanceof L.LeanToken)
            token = token.args[0];
        if (
            token instanceof L.LeanAngleBracket &&
            token.arg instanceof L.LeanArgsCommaSeparated &&
            token.arg.args.every((arg) => arg instanceof L.LeanToken)
        ) {
            token = token.arg;
        }
        if (token instanceof L.LeanToken || token instanceof L.LeanArgsCommaSeparated) return token;
    }

    sep() {
        const assign = this.args[0];
        if (assign instanceof L.LeanAssign) {
            const lhs = assign.lhs;
            if (lhs instanceof L.LeanCaret) return '';
            if (lhs instanceof L.LeanColon && lhs.lhs instanceof L.LeanCaret) return '';
        }
        return ' ';
    }

    strFormat() {
        const parts = [];
        for (let i = 0; i < this.args.length; i++) {
            const arg = this.args[i];
            if (i === 0) parts.push(this.sep());
            else if (arg instanceof L.LeanCaret);
            else if (this.semicolon && i === 1) parts.push('; '); // term-mode `have x := v; body`
            else if (
                arg instanceof L.LeanSequentialTacticCombinator &&
                (arg.newlineBehind || arg.newlineBefore)
            ) {
                parts.push('\n');
            } else parts.push(' ');
            parts.push('%s');
        }
        return this.keyword + parts.join('');
    }
}

export class Lean_set extends Lean_let {
    static { this.register(); }

    get command() {
        return 'set';
    }

    get operator() {
        return 'set';
    }
}

/** `replace h : T := proof` — same shape as `have`, but replaces the hypothesis `h`. */
export class Lean_replace extends Lean_have {
    static { this.register(); }

    get command() {
        return 'replace';
    }

    get operator() {
        return 'replace';
    }
}

export class Lean_show extends LeanSyntax {
    static { this.register(); }

    constructor(arg, indent, level, parent = null) {
        super([arg], indent, level, parent);
    }

    get stack_priority() {
        return 7;
    }

    get operator() {
        return 'show';
    }

    is_indented() {
        const parent = this.parent;
        return parent instanceof L.LeanStatements || parent instanceof L.LeanArgsNewLineSeparated;
    }

    /**
     * Bare tactic `show T` restates the goal as T (defeq). Insert intermediate `echo ⊢`
     * so the next fragment shows that goal before later tactics. When `by` / `from` is
     * attached (`show T by …` / `show T from …`), echo into that proof body instead —
     * the by/from closes the shown goal, so no trailing turnstile after the whole show.
     */
    echo() {
        for (const a of this.args) {
            if (a instanceof L.LeanBy) {
                a.echo();
                return;
            }
            if (a instanceof L.LeanFrom) {
                a.echo();
                return;
            }
        }
        const token = new L.LeanToken('⊢', this.indent, this.level);
        return [1, this, new L.LeanTactic('echo', token, this.indent, this.level)];
    }


    toJSON() {
        return {
            [this.operator]: super.toJSON(),
        };
    }

    latexFormat() {
        const f = `{\\color{#00f}${this.func}}`;
        return `${f}\\ ${Array(this.args.length).fill('%s').join('\\ ')}`;
    }

    strFormat() {
        return `${this.func} ${Array(this.args.length).fill('%s').join(' ')}`;
    }
}
