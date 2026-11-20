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

import { compile } from "../lean.js";
import { LeanColon } from "./colon.js";

const isHole = (node) => node == null || node === "_";

const regexFormat = {
    literal: (value) => value,
    group: (value) => "(" + value + ")",
    join: (parts) => parts.join(""),
};

/** @returns {string|null} regex fragment; null = hole `_`, "" = empty slot. */
function convert(node, format = regexFormat) {
    if (node === "") return "";
    if (isHole(node)) return null;
    if (typeof node === "string") return format.literal(node);
    if (Array.isArray(node)) {
        const parts = node.map((item) => convert(item, format)).filter((s) => s != null && s !== "");
        return parts.length ? format.join(parts) : null;
    }
    const entries = Object.entries(node);
    if (entries.length !== 1) return null;
    const [head, args0] = entries[0];
    const args = Array.isArray(args0) ? args0 : [args0];

    const parts = [format.literal(head)];
    for (const arg of args) {
        const frag = convert(arg, format);
        if (frag === "") continue;
        parts.push(frag == null ? format.literal("_") : format.group(frag));
    }
    return format.join(parts);
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

function dagBuilder() {
    const nodes = [];
    const ids = new Map();

    function intern(node) {
        const key = JSON.stringify(node);
        if (!ids.has(key)) {
            ids.set(key, nodes.length);
            nodes.push(node);
        }
        return ids.get(key);
    }

    return { nodes, intern };
}

/** Build the hole-regex DAG directly from a Lean node's JSON tree. */
export function json2dag(node) {
    const format = {
        literal: (token) => [token],
        group: (parts) => [{ group: parts }],
        join: (parts) => parts.flat(),
    };
    const { nodes, intern } = dagBuilder();

    function walk(parts) {
        const children = [];
        let text = "";
        function flush() {
            for (const token of text.match(/_|[^_]+/g) ?? []) children.push(intern({ token }));
            text = "";
        }
        for (const part of parts) {
            if (typeof part === "string") {
                text += part;
            } else {
                flush();
                children.push(intern({ group: walk(part.group) }));
            }
        }
        flush();
        return children;
    }

    const parts = convert(node, format) ?? ["_"];
    intern({ sequence: walk(parts) });
    return nodes;
}

/** Intern identical regex subtrees in postorder, with the root last. */
export function regex2dag(regex) {
    const tokens = regex.match(/[()_]|[^()_]+/g) ?? [];
    const { nodes, intern } = dagBuilder();
    let index = 0;

    function walk(kind) {
        const children = [];
        while (index < tokens.length && tokens[index] !== ")") {
            const token = tokens[index++];
            children.push(token === "(" ? walk("group") : intern({ token }));
        }
        if (kind === "group" && tokens[index++] !== ")") {
            throw new Error("Unclosed regex group");
        }
        return intern({ [kind]: children });
    }

    walk("sequence");
    if (index !== tokens.length) throw new Error("Unexpected closing regex parenthesis");
    return nodes;
}

/** Compute a longest valid suggestion that expands each named subtree at most once. */
export function dag2suggession(dag) {
    // State 3 represents any run of at least three pending underscores.
    // Such runs can be discarded as trailing padding, but cannot precede text.
    const pendingCounts = [0, 1, 2, 3];
    const results = [];

    function keepLongest(paths, candidate) {
        const { pending, used, text } = candidate;
        const key = (used << 2n) | BigInt(pending);
        if (text.length > (paths.get(key)?.text.length ?? -1)) paths.set(key, candidate);
    }

    for (const [id, node] of dag.entries()) {
        const transitions = pendingCounts.map((incoming) => {
            const omitted = { pending: Math.min(incoming + 1, 3), used: 0n, text: "" };
            if (node.token === "_") return [omitted];
            if (node.token !== undefined) {
                return incoming < 3
                    ? [{ pending: 0, used: 0n, text: "_".repeat(incoming) + node.token }]
                    : [];
            }

            const children = node.group ?? node.sequence;
            const head = dag[children[0]]?.token;
            const used = head && head !== "_" ? 1n << BigInt(id) : 0n;
            let paths = [{ pending: incoming, used, text: "" }];
            for (const child of children) {
                const next = new Map();
                for (const prefix of paths) {
                    for (const suffix of results[child][prefix.pending]) {
                        if ((prefix.used & suffix.used) !== 0n) continue;
                        keepLongest(next, {
                            pending: suffix.pending,
                            used: prefix.used | suffix.used,
                            text: prefix.text + suffix.text,
                        });
                    }
                }
                paths = [...next.values()];
            }
            if (node.group) paths.push(omitted);
            return paths;
        });
        results.push(transitions);
    }

    let suggestion = "";
    for (const { text } of results.at(-1)?.[0] ?? []) {
        if (text.length > suggestion.length) suggestion = text;
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

/** Return the shortest generated path token for a Lean expression. */
export function lean2path(expression) {
    const module = compile(`private lemma main : ${expression} := by\n  sorry\n`);
    const signature = module.args[0]?.assignment?.lhs;
    if (!(signature instanceof LeanColon)) return "";

    const json = signature.rhs.toJSON();
    const base = dag2suggession(json2dag(json));
    let shortest = suggestionMatches(json2regex(json), base) ? base : "";
    for (const regex of json2plural(json)) {
        const candidate = dag2suggession(regex2dag(regex));
        if ((!shortest || candidate.length < shortest.length) && suggestionMatches(regex, candidate)) {
            shortest = candidate;
        }
    }
    return shortest;
}
