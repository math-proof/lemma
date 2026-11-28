/**
 * Statement lists (`LeanStatements`).
 *
 * Multiline blocks: proof scripts after `by`, and proposition text after `:`.
 * `leanStatementsPreferWordOverTactic` lives here because only `insert_tactic`
 * uses it.
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { leanIsInfixContinue } from './utility.js';
import { LeanArgs } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

function printedSpan(node) {
    const text = String(node ?? '');
    return text === '' ? 1 : text.split('\n').length;
}

/**
 * New echo tactics are built onto their own lines. `line` is the line of that
 * new node; nodes already built at or after it move down.
 */
function placeInsertedLines(stmt, index, removedCount, inserted) {
    const old = stmt.args.slice(index, index + removedCount);
    const replaced = new Set(old);
    const root = stmt.root;
    if (!root) return;
    let at = null;
    for (const node of inserted) {
        if (node == null) continue;
        if (replaced.has(node)) {
            const line = node.line;
            at = (typeof line === 'number' ? line : (at ?? 1)) + printedSpan(node);
            continue;
        }
        if (at == null) at = typeof old[0]?.line === 'number' ? old[0].line : 1;
        Lean.shiftLines(root, at, 1);
        if (node instanceof L.LeanTactic && node.getEcho()) node.setEchoLine(at);
        else node.line = at;
        at += 1;
    }
}

/**
 * Multiline `LeanStatements` is used both for proof scripts (`by …`) and for proposition/type text after `:`.
 * Tactic names that overlap with term names (e.g. `arg`) must parse as words in the latter case.
 * @param {LeanStatements} stmts
 */
function leanStatementsPreferWordOverTactic(stmts) {
    for (let p = stmts.parent; p; p = p.parent) {
        if (p instanceof L.LeanBy || p instanceof L.LeanFrom) {
            return false;
        }
        let ch = stmts;
        while (ch.parent !== p) {
            if (!ch.parent) break;
            ch = ch.parent;
        }
        if (ch.parent !== p) continue;
        if (p instanceof L.LeanColon && p.rhs === ch) return true;
        if (p instanceof L.LeanBrace && p.arg === ch) {
            /** `repeat { simp only … }` / `try { … }` — tactic block, not a term `{ … }`. */
            let q = p.parent;
            while (q instanceof L.LeanArgsSpaceSeparated) q = q.parent;
            return !(q instanceof L.LeanTactic && q.is_inline_tactic_block());
        }
        if ((p instanceof L.Lean_rightarrow || p instanceof L.Lean_mapsto) && p.rhs === ch) return true;
    }
    return false;
}



export class LeanStatements extends LeanArgs {
    static { this.register(); }
    static lineStartsAtChild = true;

    /**
     * Body of a multi-line structure-instance literal (see `LeanBrace.openStructInstBody`): one field per line.
     * @type {boolean | undefined}
     */
    structInst = undefined;

    /** The first statement shares the line of its enclosing delimiter. */
    isInlineFirst() {
        const p = this.parent;
        return (p instanceof L.LeanTacticBlock && p.inlineFirst === true) ||
            (this.structInst === true && p?.inline === true);
    }

    get stack_priority() {
        return L.LeanColon.input_priority;
    }

    push_binary(Ctor, skipBraceShortcut = false, script) {
        const parent = this.parent;
        if (!parent) {
            // Module-level `surj y := by` (a `where` field that dedented out of the
            // structure body). There is no parent to wrap, so bind `:=` to the last statement.
            if (Ctor === L.LeanAssign && Array.isArray(this.args)) {
                let idx = this.args.length - 1;
                while (idx >= 0 && (this.args[idx] instanceof L.LeanCaret || this.args[idx] instanceof L.LeanLineComment || this.args[idx] instanceof L.LeanBlockComment))
                    idx--;
                if (idx >= 0) {
                    const origin = this.args[idx];
                    const caret = new L.LeanCaret(origin.indent, origin.level);
                    this.replace(origin, new Ctor(origin, caret, origin.indent, origin.level));
                    return caret;
                }
            }
            return undefined;
        }
        let idx = this.args.length - 1;
        while (idx >= 0) {
            const c = this.args[idx];
            if (c instanceof L.LeanCaret || c instanceof L.LeanLineComment || c instanceof L.LeanBlockComment) {
                idx--;
                continue;
            }
            break;
        }

        if ((Ctor.input_priorities?.[script] ?? Ctor.input_priority) > this.stack_priority) {
            if (idx >= 0) {
                const origin = this.args[idx];
                while (
                    this.args.length - 1 > idx &&
                    this.args[this.args.length - 1] instanceof L.LeanCaret
                ) {
                    this.args.pop();
                }
                const caret = new L.LeanCaret(origin.indent, origin.level);
                this.replace(origin, new Ctor(origin, caret, origin.indent, origin.level));
                return caret;
            }
            return super.push_binary(Ctor, skipBraceShortcut, script);
        }

        // `skipBraceShortcut` (from `insert_assign` / `insert_colon`) keeps the old parse for every `:` and for `:=`
        // outside braces. In a brace body (`{⏎ a := 1⏎ b := 2⏎ }`, or the `structInst` body of `{ a := 1⏎ b := 2 }`
        // / `{ s with⏎ … }`) `x := v` starts the next structure-instance field.
        const structField = Ctor === L.LeanAssign && (this.structInst === true || parent instanceof L.LeanBrace);
        if ((skipBraceShortcut && !structField) || (Ctor !== L.LeanAssign && Ctor !== L.LeanColon) || !(parent instanceof L.LeanBrace || structField))
            return super.push_binary(Ctor, skipBraceShortcut, script);
        if (idx < 0) return super.push_binary(Ctor, skipBraceShortcut, script);
        if (structField) this.structInst = true;
        const origin = this.args[idx];
        const caret = new L.LeanCaret(origin.indent, origin.level);
        this.replace(origin, new Ctor(origin, caret, origin.indent, origin.level));
        return caret;
    }

    insert_tactic(caret, token) {
        if (caret instanceof L.LeanCaret && leanStatementsPreferWordOverTactic(this)) {
            return this.insert_word(caret, token);
        }
        return super.insert_tactic(caret, token);
    }

    insert_semicolon(caret) {
        if (caret instanceof L.LeanTactic) return caret.insert_semicolon(caret.arg);
        // `by\n  have := e; rw …` — `;` starts the next tactic of this block.
        // Bubbling to `by` lifts the whole block onto the `by` line (`by       have`).
        const p = this.parent;
        if (p instanceof L.LeanBy || p instanceof L.LeanTacticBlock) {
            let host = null;
            for (let i = this.args.length - 1; i >= 0; i--) {
                const a = this.args[i];
                if (a instanceof L.LeanCaret || a instanceof L.LeanLineComment || a instanceof L.LeanBlockComment) continue;
                host = a;
                break;
            }
            if (host) {
                const neu = new L.LeanCaret(host.indent, host.level);
                if (host instanceof L.LeanArgsSemicolonSeparated) {
                    host.push(neu);
                    return neu;
                }
                this.replace(host, new L.LeanArgsSemicolonSeparated([host, neu], host.indent, host.level));
                return neu;
            }
        }
        return super.insert_semicolon(caret);
    }

    insert_comma(caret) {
        // `a := 1,⏎ b := 2`: a comma after a field of a structure-instance body
        if (this.structInst === true && this.args.includes(caret)) {
            const c2 = new L.LeanCaret(caret.indent, caret.level);
            this.replace(caret, new L.LeanArgsCommaSeparated([caret, c2], caret.indent, caret.level));
            return c2;
        }
        return super.insert_comma(caret);
    }

    strArgs() {
        const args = super.strArgs();
        if (!this.isInlineFirst() || !args.length) return args;
        return [String(args[0]).replace(/^ +/, ''), ...args.slice(1)];
    }

    unshift(arg) {
        if (arg instanceof L.LeanTactic && arg.tacticName === 'echo') {
            const at = typeof this.args[0]?.line === 'number'
                ? this.args[0].line
                : (typeof this.line === 'number' ? this.line : 1);
            Lean.shiftLines(this.root, at, 1);
            arg.setEchoLine(at);
        }
        return super.unshift(arg);
    }

    echo() {
        const {args} = this;
        let count = args.length;
        let void_lines = 0;
        while (count > 0) {
            const last = args[count - 1];
            if (last instanceof L.LeanCaret || last instanceof L.LeanLineComment || last instanceof L.LeanBlockComment) {
                count--;
                void_lines++;
            } else break;
        }
        let index = 0;
        for (; index < args.length - void_lines - 1; ++index) {
            const result = args[index].echo();
            if (Array.isArray(result)) {
                const length = result.shift();
                if (
                    index + 1 < args.length - void_lines &&
                    args[index + 1] instanceof L.LeanTactic &&
                    args[index + 1].tacticName === 'try' &&
                    result.length === 2 &&
                    result[0] === args[index] &&
                    result[1] instanceof L.LeanTactic &&
                    result[1].tacticName === 'echo'
                ) {
                    const e = result[1];
                    result[1] = new L.LeanTactic('try', e, e.indent, e.level);
                }
                for (const echo of result) echo.parent = this;
                // A head tactic followed by statement-level `LeanCond` lines
                // forms one multi-line alternative group (`first | …`,
                // `rcases … | …`): trailing `echo` placeholders must stay after
                // the whole group, never between the head and its `|` branches
                // (the latter generates invalid Lean: `first echo ⊢ | …`).
                let barRun = 0;
                for (let j = index + length; j < args.length - void_lines && args[j] instanceof L.LeanCond; j++) barRun++;
                const trailingEchoes = [];
                if (barRun) {
                    while (result.length > 1 && result[result.length - 1] instanceof L.LeanTactic && result[result.length - 1].tacticName === 'echo') {
                        trailingEchoes.unshift(result.pop());
                    }
                }
                placeInsertedLines(this, index, length, result);
                const increment = result.indexOf(args[index]);
                args.splice(index, length, ...result);
                if (trailingEchoes.length) {
                    const atIndex = index + result.length + barRun;
                    const at = typeof args[atIndex]?.line === 'number'
                        ? args[atIndex].line
                        : (args[atIndex - 1]?.line ?? 0) + 1;
                    Lean.shiftLines(this.root, at, trailingEchoes.length);
                    let line = at;
                    for (const echo of trailingEchoes) {
                        echo.setEchoLine(line);
                        line += 1;
                    }
                    args.splice(atIndex, 0, ...trailingEchoes);
                }
                index += increment;
            }
        }
        const tactic = args[index];
        if (tactic instanceof L.LeanTactic || tactic instanceof L.Lean_match) {
            const result = tactic.echo();
            if (Array.isArray(result)) {
                const length = result.shift();
                const pos = result.indexOf(tactic);
                if (pos >= 0) {
                    while (result.length > pos + 1) {
                        const tail = result[result.length - 1];
                        if (tail instanceof L.LeanTactic && tail.tacticName === 'echo') result.pop();
                        else break;
                    }
                }
                for (const echo of result) echo.parent = this;
                placeInsertedLines(this, index, length, result);
                args.splice(index, length, ...result);
            } else if (tactic.tacticName === 'case') {
                const arrow = tactic.arrow;
                if (arrow && arrow.rhs instanceof LeanStatements) arrow.rhs.echo();
            } else {
                const w = tactic.with;
                if (w) {
                    if (w.sep() === '\n') {
                        for (const c of w.args) c.echo();
                    } else if (tactic.sequential_tactic_combinator) {
                        const block = tactic.sequential_tactic_combinator.arg;
                        // `tactic.echo` already walked a same-line `<;>` chain.
                        // Echoing it again wraps the inserted `echo` tactic and
                        // grows one `<;> echo ⊢` per visit.
                        if (block instanceof L.LeanTacticBlock) block.echo();
                        else if (!(block instanceof L.LeanTactic && block.tacticName === 'echo'))
                            tactic.sequential_tactic_combinator.echo();
                    }
                } else if (tactic.sequential_tactic_combinator) {
                    tactic.sequential_tactic_combinator.echo();
                } else {
                    const rb = tactic.repeat_block();
                    if (rb) rb.echo();
                    const {using} = tactic;
                    if (using) using.echo();
                }
            }
        } else if (tactic instanceof L.LeanTacticBlock || tactic instanceof L.LeanIte || tactic instanceof L.LeanCalc) {
            tactic.echo();
        }
    }

    replace(oldNode, newNode) {
        const blanks = oldNode?.leadingBlanks || 0;
        super.replace(oldNode, newNode);
        if (!blanks) return;
        const host = (Array.isArray(newNode) ? newNode : [newNode]).find((n) => n && typeof n === 'object');
        if (host) host.leadingBlanks = (host.leadingBlanks || 0) + blanks;
    }

    insert_if(caret) {
        if (!(caret instanceof L.LeanCaret)) return undefined;
        const last = this.args[this.args.length - 1];
        if (last !== caret) return undefined;
        this.replace(caret, new L.LeanIte([caret], caret.indent, caret.level));
        return caret;
    }

    insert_newline(caret, newline_count, indent, next) {
        if (this.indent > indent) return super.insert_newline(caret, newline_count, indent, next);
        if (this.indent < indent) {
            if (leanIsInfixContinue(next)) {
                // `p\n    ∧ q` — the operator continues the last statement.
                // A fresh caret would be its lhs and the `∧` would share `p`'s line.
                let idx = this.args.length - 1;
                while (idx >= 0 && (this.args[idx] instanceof L.LeanCaret || this.args[idx] instanceof L.LeanLineComment || this.args[idx] instanceof L.LeanBlockComment))
                    idx--;
                const host = idx >= 0 ? this.args[idx] : null;
                if (host) {
                    host.pendingOpLead = indent;
                    return host;
                }
            } else {
                const c = this.push_args_indented(indent, newline_count);
                if (c) return c;
            }
            // See `LeanModule.insert_newline` — fall through when last arg cannot be wrapped.
        }
        // A module blank line is its own caret (the line oracle marks those).
        // Inside a statement list the extra breaks are only a gap before the
        // next statement: an empty caret there has no rendered span.
        if (this.constructor === LeanStatements && newline_count > 1) {
            const blanks = newline_count - 1;
            caret = new L.LeanCaret(indent, caret.level).stampFollowingLine(blanks);
            caret.leadingBlanks = blanks;
            this.push(caret);
            return caret;
        }
        for (let k = 0; k < newline_count; ++k) {
            // The `\n` token is the line it ends. The caret is the following line.
            caret = new L.LeanCaret(indent, caret.level).stampFollowingLine(k);
            this.push(caret);
        }
        return caret;
    }

    is_indented() {
        return false;
    }

    isProp(vars) {
        const args = this.args;
        if (args.length === 1) return args[0].isProp(vars);
    }

    toJSON(ctx = { leaves: new Map() }) {
        let args = super.toJSON(ctx);
        if (this.args.length && this.args[this.args.length - 1] instanceof L.LeanCaret) {
            args = args.slice(0, -1);
        }
        if (args.length === 1) return args[0];
        return args;
    }

    latexFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        if (n === 1) return '%s';
        const stmt = Array(n).fill('&{%s}&& ').join('\\\\\n');
        const p = this.parent;
        if (p && p instanceof L.LeanBy) return stmt;
        let align =  (p instanceof L.LeanRelational || p instanceof L.LeanBinary || p instanceof L.LeanStack || p instanceof L.LeanIte) ? 'aligned': 'align*';
        return `\\begin{${align}}\n${stmt}\n\\end{${align}}`;
    }

    relocate_last_comment() {
        for (let index = this.args.length - 1; index >= 0; --index) {
            const end = this.args[index];
            if (end.is_outsider()) {
                let self = this;
                let parent = null;
                while (self) {
                    parent = self.parent;
                    if (parent instanceof LeanStatements) break;
                    self = parent;
                }
                if (parent) {
                    const last = this.args.pop();
                    const index = parent.args.indexOf(self);
                    parent.args.splice(index + 1, 0, last);
                    last.parent = parent;
                    last.indent = parent.indent;
                    parent.relocate_last_comment();
                    break;
                }
            } else {
                if (end.is_comment()) {
                    let lemma = null;
                    let j = 0;
                    for (j = index - 1; j >= 0; --j) {
                        const stmt = this.args[j];
                        if (stmt instanceof L.Lean_lemma) {
                            lemma = stmt;
                            break;
                        }
                        if (stmt.is_comment()) continue;
                        break;
                    }
                    if (lemma) {
                        const assignment = lemma.assignment;
                        if (assignment instanceof L.LeanAssign) {
                            let proof = assignment.rhs;
                            if (proof instanceof L.LeanBy || proof instanceof L.LeanCalc) {
                                proof = proof.arg;
                                if (proof instanceof LeanStatements) {
                                    for (let i = j + 1; i <= index; ++i) proof.push(this.args[i]);
                                    this.args.splice(j + 1, index - j);
                                    break;
                                }
                            } else if (proof instanceof L.LeanArgsNewLineSeparated) {
                                for (let i = j + 1; i <= index; ++i) proof.push(this.args[i]);
                                this.args.splice(j + 1, index - j);
                                break;
                            }
                        }
                    }
                }
                end.relocate_last_comment();
                break;
            }
        }
    }

    strFormat() {
        const n = this.args.length;
        if (n === 0) return '';
        let format = this.args.map((arg, i) => {
            const gap = arg?.leadingBlanks || 0;
            const prev = i > 0 ? this.args[i - 1] : null;
            if (
                gap === 0 &&
                arg instanceof L.LeanLineComment &&
                prev &&
                Lean.lastSourceLine(prev) === arg.line
            )
                return ' %s';
            return (i === 0 ? '\n'.repeat(gap) : '\n' + '\n'.repeat(gap)) + '%s';
        }).join('');
        if (this.parent instanceof L.LeanBrace && !this.parent.inline) {
            const pad = this.parent.closeIndent;
            // `closeIndent` is set only when `}` begins the following line.
            format = pad !== undefined
                ? `\n${format}\n${' '.repeat(pad)}`
                : `\n${format} `;
        }
        return format;
    }

    swap_echo_star(syntax, statements) {
        const args = this.args;
        for (let i = 0; i < args.length; ++i) {
            const echo = args[i];
            if (
                echo instanceof L.LeanTactic &&
                echo.tacticName === 'echo' &&
                echo.arg instanceof L.LeanToken &&
                echo.arg.text === '*'
            ) {
                [args[i], args[i + 1]] = [args[i + 1], args[i]];
                i++;
            }
        }
        for (const stmt of this.args) statements.push(...stmt.split(syntax));
    }

    /** Port of LeanStatements::push_line_comment. Stops bubbling to root. */
    push_line_comment(comment) {
        const line = new L.LeanLineComment(comment, this.indent, this.level);
        this.push(line);
        return line;
    }
}
