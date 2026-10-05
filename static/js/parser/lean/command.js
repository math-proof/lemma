/**
 * Top-level commands (`LeanCommand`, `import` / `open` / `set_option` / `namespace`).
 *
 * `LeanUnary`, `LeanCaret`, `LeanProperty`, and `LeanToken` already exist and
 * are passed in. `LeanArgsSpaceSeparated` is filled on `commandLate`.
 * `LEAN_CLASSES` is the shared registry (`classRegistry.map`). This factory
 * does not import `lean.js`. PHP `append` still writes `$this->sql`, and PHP
 * `open` stays `'open'` (JS may render `open scoped`).
 *
 * @param {object} deps
 * @param {Function} deps.LeanUnary
 * @param {Function} deps.LeanCaret
 * @param {Function} deps.LeanProperty
 * @param {Function} deps.LeanToken
 * @param {{map: object|null}} deps.classRegistry
 * @param {object} deps.commandLate
 */
export function createCommandFamily(deps) {
    const {
        LeanUnary,
        LeanCaret,
        LeanProperty,
        LeanToken,
        classRegistry,
        commandLate,
    } = deps;

    function lateCtor(name) {
        function Ctor() {}
        return new Proxy(Ctor, {
            construct(_target, args) {
                const real = commandLate[name];
                if (real == null) throw new Error(`${name} used before command registration`);
                return new real(...args);
            },
            get(_target, prop) {
                const real = commandLate[name];
                if (real == null) throw new Error(`${name} used before command registration`);
                if (prop === Symbol.hasInstance) return (inst) => inst instanceof real;
                const value = real[prop];
                return typeof value === 'function' ? value.bind(real) : value;
            },
        });
    }
    const LeanArgsSpaceSeparated = lateCtor('LeanArgsSpaceSeparated');
    const LEAN_CLASSES = new Proxy(Object.create(null), {
        get(_target, key) {
            const map = classRegistry.map;
            if (map == null) throw new Error('LEAN_CLASSES used before command registration');
            return map[key];
        },
    });

    /** Top-level commands (`import` / `open` / `set_option` / `namespace`): `stack_priority` 27 except `namespace` (inherits unary 47). */
    class LeanCommand extends LeanUnary {
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
    class Lean_import extends LeanCommand {
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
            const Ctor = LEAN_CLASSES[func];
            const level = this.arg.level;
            const c = new LeanCaret(this.indent, level);
            this.arg = new Ctor(c, this.indent, level);
            return c;
        }

        push_attr(caret) {
            if (caret === this.arg) {
                const $new = new LeanCaret(this.indent, caret.level);
                this.arg = new LeanProperty(this.arg, $new, this.indent, caret.level);
                return $new;
            }
            throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
        }
    }

    class Lean_open extends LeanCommand {
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
            const Ctor = LEAN_CLASSES[func];
            const level = this.arg.level;
            const c = new LeanCaret(this.indent, level);
            this.arg = new Ctor(c, this.indent, level);
            return c;
        }

        push_attr(caret) {
            if (caret === this.arg) {
                const $new = new LeanCaret(this.indent, caret.level);
                this.arg = new LeanProperty(this.arg, $new, this.indent, caret.level);
                return $new;
            }
            throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
        }
    }

    /** `set_option %s`. */
    class Lean_set_option extends LeanCommand {
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
            const Ctor = LEAN_CLASSES[func];
            const level = this.arg.level;
            const c = new LeanCaret(this.indent, level);
            this.arg = new Ctor(c, this.indent, level);
            return c;
        }

        echo() {
            const {arg} = this;
            if (arg instanceof LeanArgsSpaceSeparated && arg.args.length === 2) {
                const {args} = arg;
                if (args[0] instanceof LeanToken && args[1] instanceof LeanToken && args[0].text === 'maxHeartbeats') {
                    args[1].text = String(parseInt(String(args[1].text), 10) * 5);
                }
            }
        }

        push_attr(caret) {
            if (caret === this.arg) {
                const $new = new LeanCaret(this.indent, caret.level);
                this.arg = new LeanProperty(this.arg, $new, this.indent, caret.level);
                return $new;
            }
            throw new Error(`push_attr is unexpected for ${this.constructor.name}`);
        }
    }

    /** `namespace %s`. */
    class Lean_namespace extends LeanCommand {
        get operator() {
            return 'namespace';
        }
    }

    return {
        LeanCommand,
        Lean_import,
        Lean_open,
        Lean_set_option,
        Lean_namespace,
    };
}
