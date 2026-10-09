/**
 * Top-level commands (`LeanCommand`, `import` / `open` / `set_option` / `namespace`).
 *
 * PHP `append` still writes `$this->sql`, and PHP `open` stays `'open'`
 * (JS may render `open scoped`).
 *
 * Base classes (the ones in `extends`) are imported from the modules that
 * define them; every other class is read from `Lean.classes` (`L.X`) at
 * call time, so the import graph follows the inheritance tree.
 */
import { LeanUnary } from './abstract.js';
import { Lean } from './base.js';

const L = Lean.classes;

/** Top-level commands (`import` / `open` / `set_option` / `namespace`): `stack_priority` 27 except `namespace` (inherits unary 47). */
export class LeanCommand extends LeanUnary {
    static { this.register(); }

    get command() {
        return this.operator;
    }

    is_indented() {
        return false;
    }

    toJSON() {
        return { [this.func]: this.arg.toJSON() };
    }

    latexFormat() {
        return `${this.command} %s`;
    }

    strFormat() {
        return `${this.operator} %s`;
    }
}

/** `import %s`. */
export class Lean_import extends LeanCommand {
    static { this.register(); }

    get stack_priority() {
        return 27;
    }
    get operator() {
        return 'import';
    }

    append(func, type) {
        if (typeof func !== 'string') {
            throw new Error(`append is unexpected for ${this.constructor.name}`);
        }
        const Ctor = L[func];
        const level = this.arg.level;
        const c = new L.LeanCaret(this.indent, level);
        this.arg = new Ctor(c, this.indent, level);
        return c;
    }

    push_attr(caret) {
        if (caret === this.arg) {
            const $new = new L.LeanCaret(this.indent, caret.level);
            this.arg = new L.LeanProperty(this.arg, $new, this.indent, caret.level);
            return $new;
        }
        throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
    }
}

export class Lean_open extends LeanCommand {
    static { this.register(); }

    get stack_priority() {
        return 27;
    }
    get operator() {
        return this.scoped ? 'open scoped' : 'open';
    }

    append(func, type) {
        if (typeof func !== 'string') {
            throw new Error(`append is unexpected for ${this.constructor.name}`);
        }
        const Ctor = L[func];
        const level = this.arg.level;
        const c = new L.LeanCaret(this.indent, level);
        this.arg = new Ctor(c, this.indent, level);
        return c;
    }

    push_attr(caret) {
        if (caret === this.arg) {
            const $new = new L.LeanCaret(this.indent, caret.level);
            this.arg = new L.LeanProperty(this.arg, $new, this.indent, caret.level);
            return $new;
        }
        throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
    }
}

/** `set_option %s`. */
export class Lean_set_option extends LeanCommand {
    static { this.register(); }

    get stack_priority() {
        return 27;
    }
    get operator() {
        return 'set_option';
    }

    append(func, type) {
        if (typeof func !== 'string') {
            throw new Error(`append is unexpected for ${this.constructor.name}`);
        }
        const Ctor = L[func];
        const level = this.arg.level;
        const c = new L.LeanCaret(this.indent, level);
        this.arg = new Ctor(c, this.indent, level);
        return c;
    }

    echo() {
        const {arg} = this;
        if (arg instanceof L.LeanArgsSpaceSeparated && arg.args.length === 2) {
            const {args} = arg;
            if (args[0] instanceof L.LeanToken && args[1] instanceof L.LeanToken && args[0].text === 'maxHeartbeats') {
                args[1].text = String(parseInt(String(args[1].text), 10) * 5);
            }
        }
    }

    push_attr(caret) {
        if (caret === this.arg) {
            const $new = new L.LeanCaret(this.indent, caret.level);
            this.arg = new L.LeanProperty(this.arg, $new, this.indent, caret.level);
            return $new;
        }
        throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
    }
}

/** `namespace %s`. */
export class Lean_namespace extends LeanCommand {
    static { this.register(); }

    get operator() {
        return 'namespace';
    }
}
