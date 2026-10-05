/**
 * Pipeline dot `|>.` (`LeanMethodChaining`).
 *
 * `LeanBinary` already exists and is passed in. This factory does not
 * import `lean.js`.
 *
 * @param {object} deps
 * @param {Function} deps.LeanBinary
 */
export function createPipelineFamily(deps) {
    const { LeanBinary } = deps;

    /** Pipeline `|>.`. */
    class LeanMethodChaining extends LeanBinary {
        static input_priority = 67;

        get stack_priority() {
            return 59;
        }

        latexFormat() {
            return '%s\\ \\texttt{|>.}%s';
        }

        sep() {
            return '';
        }

        strFormat() {
            return '%s |>.%s';
        }
    }

    return {
        LeanMethodChaining,
    };
}
