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
 * Hole policy: a big operator's domain is dropped when the same domain is
 * already given by a big operator nested in its scope — the inner occurrence
 * is the informative one. Hence an outer `∑ x ∈ X ∪ {y'}, …` whose body holds
 * `∑ x ∈ X ∪ {y'}, a[x]` becomes `Sum_(…)`, while the inner one keeps
 * `Sum(Union_(Brace_))(Get__)`.
 */

/** Heads whose JSON arguments are `[domain, scope]`. */
const BIG_OP_HEADS = new Set([
    "All", "Any", "Sum", "Prod", "Prob", "Expect", "Var",
    "Lim", "Sup", "Inf", "Max", "Min", "Int",
]);

const isHole = (node) => node == null || node === "_";
const isNode = (node) => !!node && typeof node === "object" && !Array.isArray(node);

/** Does `scope` contain a big operator whose domain equals `domain`? */
function hasNestedDomain(scope, domain) {
    if (!isNode(scope)) return false;
    const want = JSON.stringify(domain);
    for (const [head, args] of Object.entries(scope)) {
        if (!Array.isArray(args)) continue;
        if (BIG_OP_HEADS.has(head) && args.length === 2 && JSON.stringify(args[0]) === want)
            return true;
        if (args.some((arg) => hasNestedDomain(arg, domain))) return true;
    }
    return false;
}

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
    let [head, args] = entries[0];
    if (!Array.isArray(args)) args = [args];

    if (BIG_OP_HEADS.has(head) && args.length === 2 && !isHole(args[0]) &&
        hasNestedDomain(args[1], args[0])) {
        args = ["_", args[1]];
    }

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
