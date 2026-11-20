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
 * Big-operator domains come from `LeanBigOperator.jsonDomain` (rhs of a typed
 * or membership binder); every domain present in the JSON is rendered.
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

function matchImplyHoleRegex(regex, suggestion) {
    const pattern = new RegExp("^" + regex.replaceAll("(", "(_|") + "$");
    // Each explicit hole or omitted group can contribute one padding character.
    const maxPadding = regex.match(/[_\(]/g)?.length ?? 0;
    for (let padding = 0; padding <= maxPadding; padding++) {
        if (pattern.test(suggestion + "_".repeat(padding))) return true;
    }
    return false;
}

/** Check a path suggestion against a stored hole-regex. */
export function suggestionMatches(regex, suggestion) {
    return typeof regex === "string" && typeof suggestion === "string" &&
        suggestion.length > 0 && !/_{3,}|_$/.test(suggestion) &&
        matchImplyHoleRegex(regex, suggestion);
}

/** Walk the stored groups and return the longest valid suggestion. */
export function regex2suggestion(regex) {
    const tokens = regex.match(/[()]|_+|[^()_]+/g) ?? [];
    let index = 0;

    function keepLongest(states, pending, path) {
        if (path.length > (states.get(pending)?.length ?? -1)) states.set(pending, path);
    }

    // Keep the best prefix for each run of pending underscores. A run may
    // exceed two only while it can still become trailing padding.
    function walk(states) {
        while (index < tokens.length && tokens[index] !== ")") {
            const token = tokens[index++];
            const next = new Map();
            if (token === "(") {
                for (const [pending, path] of walk(states)) keepLongest(next, pending, path);
                index++;
                for (const [pending, path] of states) keepLongest(next, pending + 1, path);
            } else if (token.startsWith("_")) {
                for (const [pending, path] of states) keepLongest(next, pending + token.length, path);
            } else {
                for (const [pending, path] of states) {
                    if (pending <= 2) keepLongest(next, 0, path + "_".repeat(pending) + token);
                }
            }
            states = next;
        }
        return states;
    }

    let suggestion = "";
    for (const path of walk(new Map([[0, ""]])).values()) {
        if (path.length > suggestion.length && suggestionMatches(regex, path)) suggestion = path;
    }
    return suggestion;
}

/** Canonical text, used only to decide whether two arguments are identical. */
function canon(node) {
    if (Array.isArray(node)) return `[${node.map(canon).join(",")}]`;
    if (node && typeof node === "object") {
        return `{${Object.keys(node).sort().map((k) => k + ":" + canon(node[k])).join(",")}}`;
    }
    return JSON.stringify(node);
}

const headOf = (node) =>
    node && typeof node === "object" && !Array.isArray(node) && Object.keys(node).length === 1
        ? Object.keys(node)[0]
        : null;
const argsOf = (node) => {
    const value = node[headOf(node)];
    return Array.isArray(value) ? value : [value];
};

/** Keep matching subtrees and replace divergent positions with holes. */
function commonShape(nodes) {
    const first = nodes[0];
    const key = canon(first);
    if (nodes.every((node) => canon(node) === key)) return first;

    const head = headOf(first);
    if (!head || !nodes.every((node) => headOf(node) === head)) return "_";

    const children = nodes.map(argsOf);
    if (!children.every((args) => args.length === children[0].length)) return "_";
    return { [head]: children[0].map((_, i) => commonShape(children.map((args) => args[i]))) };
}

/**
 * JSON trees with one or more S-plural collapses applied.
 *
 * A node whose arguments all share one head collapses into a single head that
 * absorbs the repeated one: `Cond[Get…, Get…]` → `CondGetS`, `Lt[Abs…, Abs…]` →
 * `LtAbsS`. The collapsed head retains the common shape of the repeated
 * arguments. If they differ and share no child structure, it leaves one hole
 * per original argument.
 */
function pluralTrees(node) {
    if (node == null || typeof node !== "object") return [];
    if (Array.isArray(node)) return pluralChildren(node);
    const head = headOf(node);
    if (!head) return [];
    const args = argsOf(node);
    const out = [];

    const heads = args.map(headOf);
    if (args.length >= 2 && heads.every((h) => h && h === heads[0])) {
        const shared = heads[0];
        const shape = commonShape(args);
        const children = headOf(shape) ? argsOf(shape) : [];
        const identical = args.every((arg) => canon(arg) === canon(args[0]));
        const collapsed = identical || children.some((child) => !isHole(child) && child !== "")
            ? children
            : args.map(() => "_");
        const collapsedTree = { [head + shared + "S"]: collapsed };
        out.push(collapsedTree);
        if (collapsed.length >= 2 && collapsed.every((child) => canon(child) === canon(collapsed[0]))) {
            out.push(...pluralTrees(collapsedTree));
        }
    }

    for (const children of pluralChildren(args)) out.push({ [head]: children });
    return out;
}

function pluralChildren(children) {
    let combinations = [[]];
    for (const child of children) {
        const choices = [child, ...pluralTrees(child)];
        combinations = combinations.flatMap((prefix) => choices.map((choice) => [...prefix, choice]));
    }
    // The first combination uses the original child at every position.
    return combinations.slice(1);
}

/**
 * S-plural hole regexes for a `toJSON()` tree, including successive collapses
 * and sibling combinations.
 * @param {object|string} node result of `LeanNode.toJSON()`
 * @returns {string[]} e.g. `Prob_(Cond(Get_(Add_(1)))(Get__))` → `Prob_(CondGetS__)`
 */
export function json2plural(node) {
    return [...new Set(pluralTrees(node).map((tree) => json2regex(tree)))];
}
