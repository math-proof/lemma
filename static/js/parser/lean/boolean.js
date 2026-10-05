/**
 * Abstract boolean-valued binary base (`LeanBinaryBoolean`).
 *
 * Relational comparisons, membership, and logic connectives extend this.
 * `LeanBinary`, `LeanProp`, `LeanCaret`, and `LeanColon` already exist and
 * are passed in. Argument lists and `LeanStatements` are filled on
 * `booleanLate`. This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinary
 * @param {Function} deps.LeanProp
 * @param {Function} deps.LeanCaret
 * @param {Function} deps.LeanColon
 * @param {{map: object|null}} deps.classRegistry
 * @param {object} deps.booleanLate
 */
export function createBooleanFamily(deps) {
    const {
        LeanBinary,
        LeanProp,
        LeanCaret,
        LeanColon,
        classRegistry,
        booleanLate,
    } = deps;
    const LEAN_CLASSES = new Proxy(Object.create(null), {
        get(_target, key) {
            const map = classRegistry.map;
            if (map == null) throw new Error('LEAN_CLASSES used before boolean registration');
            return map[key];
        },
    });
    function lateCtor(name) {
        function Ctor() {}
        return new Proxy(Ctor, {
            construct(_target, args) {
                const real = booleanLate[name];
                if (real == null) throw new Error(`${name} used before boolean registration`);
                return new real(...args);
            },
            get(_target, prop) {
                const real = booleanLate[name];
                if (real == null) throw new Error(`${name} used before boolean registration`);
                if (prop === Symbol.hasInstance) return (inst) => inst instanceof real;
                const value = real[prop];
                return typeof value === 'function' ? value.bind(real) : value;
            },
        });
    }
    const LeanArgsNewLineSeparated = lateCtor('LeanArgsNewLineSeparated');
    const LeanArgsSpaceSeparated = lateCtor('LeanArgsSpaceSeparated');
    const LeanStatements = lateCtor('LeanStatements');

    class LeanBinaryBoolean extends LeanProp(LeanBinary) {
        append(new_, type) {
            const {indent, level} = this;
            const caret = new LeanCaret(indent, level);
            if (typeof new_ === 'string') {
                const Ctor = LEAN_CLASSES[new_];
                const newNode = new Ctor(caret, indent, level);
                this.rhs = new LeanArgsSpaceSeparated([this.rhs, newNode], indent, level);
                return caret;
            } else {
                this.parent.replace(this, new LeanArgsSpaceSeparated([this, new_], indent, level));
                return new_;
            }
        }

        insert_colon(caret) {
            if (caret === this.rhs) {
                const newCaret = new LeanCaret(caret.indent, caret.level);
                this.parent.replace(this, new LeanColon(this, newCaret, caret.indent, caret.level));
                return newCaret;
            }
            return caret.push_binary(LeanColon);
        }

        insert_newline(caret, newline_count, indent, next) {
            if (this.rhs === caret && caret instanceof LeanCaret && indent >= this.indent) {
                caret.indent = indent;
                return caret;
            }
            if (this.rhs === caret && indent > this.indent) {
                return this.parent.push_args_indented(indent, newline_count, false);
            }
            return super.insert_newline(caret, newline_count, indent, next);
        }

        is_indented() {
            const {parent} = this;
            return parent instanceof LeanStatements || (parent instanceof LeanArgsNewLineSeparated && this.indent > 0);
        }

        sep() {
            return this.rhs instanceof LeanStatements ? '\n' : ' ';
        }

        strFormat() {
            const sep = this.sep();
            return `%s ${this.operator}${sep}%s`;
        }
    }

    return {
        LeanBinaryBoolean,
    };
}
