/**
 * Lazy application `<|` (`Lean_lazy`).
 *
 * `a <| b` is `b a`, low precedence and right-associative. `LeanBinary`
 * already exists and is passed in. PHP `operator`, `sep`, and `strFormat`
 * stay in the PHP class; JS keeps only `input_priority` and `stack_priority`.
 * This factory does not import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinary
 */
export function createLazyFamily(deps) {
    const { LeanBinary } = deps;

    /** `<|` lazy application: `a <| b` = `b a`. Low precedence, right-associative. */
    class Lean_lazy extends LeanBinary {
        static input_priority = 20;
        get stack_priority() {
            return 19;
        }
    }

    return {
        Lean_lazy,
    };
}
