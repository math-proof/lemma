/**
 * `json2regex`: turn the `toJSON()` tree of a Lean node into a stored
 * hole-regex string (the `regex` field of `mjs/regression/*.json`).
 *
 * Shape rules:
 * - `"_"` is a hole; `""` is an empty slot and contributes nothing at all;
 *   a numeric string is a literal.
 * - `{Head: [args…]}` → `Head` followed by each argument, parenthesised when
 *   it is not a hole: `{"Get":["_","0"]}` → `Get_(0)`, `{"Card":["_"]}` → `Card_`.
 * - `{"Get":[obj, {Slice: [lo, hi]}]}` keeps both constructors; the empty lower
 *   bound of `s[:k]` is dropped, so it becomes `Get_(Slice_)`.
 *
 * Redundant binder domains are already holed by `LeanBigOperator.toJSON`
 * (stacked big operators), so no hole policy lives here.
 */

const isHole = (node) => node == null || node === "_";

/** @returns {string|null} regex fragment; null = hole `_`, "" = empty slot. */
function convert(node) {
    if (node === "") return "";
    if (isHole(node)) return null;
    if (typeof node === "string") return node;
    if (Array.isArray(node)) {
        const parts = node.map(convert).filter((s) => s != null && s !== "");
        return parts.length ? parts.join("") : null;
    }
    const entries = Object.entries(node);
    if (entries.length !== 1) return null;
    const [head, args0] = entries[0];
    const args = Array.isArray(args0) ? args0 : [args0];

    let out = head;
    for (const arg of args) {
        const frag = convert(arg);
        if (frag === "") continue;
        out += frag == null ? "_" : "(" + frag + ")";
    }
    return out;
}

/**
 * @param {object|string} node result of `LeanNode.toJSON()`
 * @returns {string} stored hole regex (`_` when the whole node is a hole)
 */
export function json2regex(node) {
    return convert(node) ?? "_";
}
