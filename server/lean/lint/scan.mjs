/**
 * Shared scanning helpers for the lemma linter (`./index.mjs`).
 *
 * The lean.js parse tree (`static/js/parser/lean.js`) carries no source positions (no line / column on any node),
 * so the rules work on the source text with comments and string literals blanked out (line / column preserved)
 * plus a bracket-aware scanner; that is enough for the layout rules and the token-level tactic rules.
 */

/**
 * `source` with comments (`-- …`, nested `/- … -/`, doc-strings `/-- … -/`) and string literals blanked out;
 * newlines are kept, so line numbers and columns are unchanged.
 * @param {string} source
 */
export function blankLeanComments(source) {
    const s = String(source ?? '');
    let out = '';
    let depth = 0;
    let inString = false;
    for (let i = 0; i < s.length; i++) {
        const c = s[i];
        const d = s[i + 1];
        const blank = (ch) => (ch === '\n' ? '\n' : ' ');
        if (depth > 0) {
            if (c === '/' && d === '-') { depth++; out += '  '; i++; continue; }
            if (c === '-' && d === '/') { depth--; out += '  '; i++; continue; }
            out += blank(c);
            continue;
        }
        if (inString) {
            if (c === '\\' && d != null) { out += blank(c) + blank(d); i++; continue; }
            if (c === '"') inString = false;
            out += blank(c);
            continue;
        }
        if (c === '/' && d === '-') { depth = 1; out += '  '; i++; continue; }
        if (c === '-' && d === '-') {
            while (i < s.length && s[i] !== '\n') { out += ' '; i++; }
            if (i < s.length) out += '\n';
            continue;
        }
        if (c === "'" && d === '"' && s[i + 2] === "'") { out += '   '; i += 2; continue; } // char literal '"'
        if (c === '"') { inString = true; out += ' '; continue; }
        out += c;
    }
    return out;
}

const OPEN = { '(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄', '⁅': '⁆' };
const CLOSE = { ')': '(', ']': '[', '}': '{', '⟩': '⟨', '⦄': '⦃', '⁆': '⁅' };
const IDENT_CHAR = /[\p{L}\p{N}_'!?.₀-₉ₐ-ₜ]/u;

/** identifier-ish character (Lean names: letters, digits, `_`, `'`, `!`, `?`, subscripts) */
export const isIdentChar = (ch) => ch != null && IDENT_CHAR.test(ch);

/**
 * Prepared view of a Lean file.
 * @param {string} source
 */
export function prepare(source) {
    const src = String(source ?? '');
    const raw = src.split(/\r?\n/);
    const code = blankLeanComments(src).split(/\r?\n/);
    // char literals of brackets, e.g. `'('`, must not count as brackets
    for (let i = 0; i < code.length; i++) {
        code[i] = code[i].replace(/(^|[^\p{L}\p{N}_'.\]])'([()[\]{}⟨⟩])'/gu, (m, p) => `${p}   `);
    }
    const indent = code.map((l) => (/^\s*$/.test(l) ? -1 : l.length - l.trimStart().length));

    // bracket structure over the whole file: for every line, the stack of open brackets at its start,
    // and for every open bracket its matching close position
    const stackAtLineStart = [];
    const pairs = new Map(); // `${line}:${col}` of an opener -> { line, col } of its closer
    const stack = [];
    for (let i = 0; i < code.length; i++) {
        stackAtLineStart.push(stack.map((e) => e.ch));
        const l = code[i];
        for (let j = 0; j < l.length; j++) {
            const ch = l[j];
            if (OPEN[ch]) stack.push({ ch, line: i, col: j });
            else if (CLOSE[ch]) {
                // tolerate mismatches: pop up to the matching opener if any
                let k = stack.length - 1;
                while (k >= 0 && stack[k].ch !== CLOSE[ch]) k--;
                if (k < 0) continue;
                const o = stack[k];
                stack.length = k;
                pairs.set(`${o.line}:${o.col}`, { line: i, col: j });
            }
        }
    }
    return { raw, code, indent, stackAtLineStart, pairs };
}

/** matching closer of the opener at (line, col), or null */
export function closerOf(P, line, col) {
    return P.pairs.get(`${line}:${col}`) ?? null;
}

/**
 * Walk the characters of `text` keeping the bracket depth; `fn(ch, j, depth, stackTop)` returns true to stop.
 * The depth is the depth *before* `ch` is applied when `ch` is an opener, after when it is a closer.
 */
export function walk(text, fn, initial = []) {
    const st = [...initial];
    for (let j = 0; j < text.length; j++) {
        const ch = text[j];
        if (CLOSE[ch] && st.length && st[st.length - 1] === CLOSE[ch]) st.pop();
        if (fn(ch, j, st.length, st[st.length - 1]) === true) return j;
        if (OPEN[ch]) st.push(ch);
    }
    return -1;
}

/** split `text` at top-level (depth 0) occurrences of `sep` (a string) */
export function splitTop(text, sep) {
    const parts = [];
    let last = 0;
    walk(text, (ch, j, depth) => {
        if (depth === 0 && text.startsWith(sep, j)) {
            parts.push(text.slice(last, j));
            last = j + sep.length;
        }
    });
    parts.push(text.slice(last));
    return parts;
}

/** index of the first top-level occurrence of a regex-tested token in `text` (or -1) */
export function findTop(text, test) {
    return walk(text, (ch, j, depth) => depth === 0 && test(text, j));
}

/** words (identifiers) in a code string */
export function words(text) {
    return text.match(/[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*/gu) ?? [];
}

/** whole-word occurrence test for a Lean identifier (dots count as separators on the left only) */
export function hasWord(text, name) {
    if (!name) return false;
    let from = 0;
    for (;;) {
        const k = text.indexOf(name, from);
        if (k < 0) return false;
        const before = text[k - 1];
        const after = text[k + name.length];
        if (!(before && /[\p{L}\p{N}_'!?₀-₉ₐ-ₜ.]/u.test(before)) && !(after && /[\p{L}\p{N}_'!?₀-₉ₐ-ₜ]/u.test(after))) return true;
        from = k + 1;
    }
}

/** count of whole-word occurrences */
export function countWord(text, name) {
    let n = 0;
    let from = 0;
    for (;;) {
        const k = text.indexOf(name, from);
        if (k < 0) return n;
        const before = text[k - 1];
        const after = text[k + name.length];
        if (!(before && /[\p{L}\p{N}_'!?₀-₉ₐ-ₜ.]/u.test(before)) && !(after && /[\p{L}\p{N}_'!?₀-₉ₐ-ₜ]/u.test(after))) n++;
        from = k + 1;
    }
}

const DECL_RE = /^((?:@\[[^\]]*\]\s*)?)((?:(?:private|protected|noncomputable|unsafe|partial|nonrec)\s+)*)(lemma|theorem|def|abbrev|instance|example|structure|class|inductive|opaque|axiom)\b\s*([^\s:({[⦃]*)/;
const MARKER_RE = /^\s*--\s*(given|imply|proof)\s*$/;

/**
 * Top-level declarations: { kind, name, attrs, attrLine, line (0-based decl line), end (exclusive), markers }.
 * A declaration runs until the next line with code at column 0.
 */
export function findDecls(P) {
    const { code, raw } = P;
    const decls = [];
    for (let i = 0; i < code.length; i++) {
        const m = DECL_RE.exec(code[i]);
        if (!m) continue;
        let attrs = m[1] ? m[1].trim() : '';
        let attrLine = m[1] ? i : -1;
        if (!attrs) {
            // `@[…]` on the line(s) above
            let k = i - 1;
            while (k >= 0 && /^\s*$/.test(code[k]) && !/^@\[/.test(raw[k])) k--;
            if (k >= 0 && /^@\[[^\]]*\]\s*$/.test(code[k])) { attrs = code[k].trim(); attrLine = k; }
        }
        let end = i + 1;
        while (end < code.length && !/^\S/.test(code[end])) end++;
        // trailing blank lines do not belong to the declaration
        let last = end;
        while (last > i + 1 && /^\s*$/.test(code[last - 1])) last--;
        const markers = {};
        for (let k = i + 1; k < last; k++) {
            const mm = MARKER_RE.exec(raw[k]);
            if (mm && markers[mm[1]] == null) markers[mm[1]] = k;
        }
        decls.push({ kind: m[3], name: m[4], attrs, attrLine, line: i, end: last, markers });
        i = end - 1;
    }
    return decls;
}

/**
 * Signature of a lemma / theorem: binder groups up to the conclusion colon, the conclusion colon and the `:=`.
 * Positions are { line, col } (0-based).
 */
export function parseSignature(P, decl) {
    const { code } = P;
    const groups = [];
    let colon = null;
    const cands = []; // top-level `:=` (after the binders), with the number of have/let-like keywords before each
    let keywords = 0;
    const st = [];
    let cur = null;
    const m = DECL_RE.exec(code[decl.line]);
    const startCol = m ? m[0].length : 0;
    outer: for (let i = decl.line; i < decl.end; i++) {
        const l = code[i];
        for (let j = i === decl.line ? startCol : 0; j < l.length; j++) {
            const ch = l[j];
            if (st.length === 0) {
                if (colon && /[a-zA-Z]/.test(ch) && !/[\p{L}\p{N}_'.]/u.test(l[j - 1] ?? ' ')) {
                    const w = /^(have|haveI|let|letI|obtain|set|generalize)(?![\p{L}\p{N}_'])/u.exec(l.slice(j));
                    if (w) keywords++;
                }
                if (OPEN[ch]) {
                    cur = colon ? null : { open: ch, line: i, col: j, text: '' };
                    st.push(ch);
                    continue;
                }
                if (ch === ':' && l[j + 1] === '=') {
                    cands.push({ line: i, col: j, keywords });
                    if (!colon) break outer;
                    j++;
                    continue;
                }
                if (ch === ':' && !colon) colon = { line: i, col: j };
                if (ch === '|' && !colon) break outer; // pattern-matching definition
                continue;
            }
            if (CLOSE[ch] && st[st.length - 1] === CLOSE[ch]) {
                st.pop();
                if (st.length === 0 && cur) {
                    cur.endLine = i;
                    cur.endCol = j;
                    groups.push(cur);
                    cur = null;
                    continue;
                }
            } else if (OPEN[ch]) st.push(ch);
            if (cur) cur.text += ch;
        }
        if (cur) cur.text += '\n';
    }
    let assign = null;
    if (!colon) assign = cands[0] ?? null;
    else if (decl.markers.proof != null) {
        const before = cands.filter((c) => c.line < decl.markers.proof);
        assign = before[before.length - 1] ?? cands[0] ?? null;
    } else {
        // the first `:=` not consumed by a `have` / `let` / … inside the conclusion
        assign = cands.find((c, k) => c.keywords <= k) ?? cands[0] ?? null;
    }
    if (assign) assign = { line: assign.line, col: assign.col };
    for (const g of groups) Object.assign(g, parseBinder(g));
    return { groups, colon, assign };
}

/** `{a b : T := v}` → { kind, names, type, deflt } */
export function parseBinder(g) {
    let open = g.open;
    let text = g.text;
    if (open === '{' && text.startsWith('{') && text.endsWith('}')) { open = '⦃'; text = text.slice(1, -1); }
    const kind = { '(': 'explicit', '{': 'implicit', '[': 'instImplicit', '⦃': 'strictImplicit' }[open] ?? 'other';
    const flat = text.replace(/\s+/g, ' ').trim();
    const k = findTop(flat, (t, j) => t[j] === ':' && t[j + 1] !== '=');
    const a = findTop(flat, (t, j) => t[j] === ':' && t[j + 1] === '=');
    let names = [];
    let type = flat;
    let deflt = null;
    if (k >= 0 && (a < 0 || k < a)) {
        names = flat.slice(0, k).trim().split(/\s+/).filter(Boolean);
        type = (a >= 0 ? flat.slice(k + 1, a) : flat.slice(k + 1)).trim();
        if (a >= 0) deflt = flat.slice(a + 2).trim();
        if (names.some((n) => !/^[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ.]*$/u.test(n))) { names = []; type = flat; deflt = null; }
    }
    return { kind, names, type, deflt, flat };
}
