/**
 * Indentation and proof-body rules (tactic conventions).
 */
import { parseSignature, walk, closerOf, countWord, hasWord } from './scan.mjs';

/** code lines of every declaration body (after the signature's `:=`): [{ line, from }] (from: first column) */
function bodies(ctx) {
    const out = [];
    for (const d of ctx.decls) {
        const sig = d.sig ?? parseSignature(ctx.P, d);
        d.sig = sig;
        if (!sig.assign) continue;
        const lines = [];
        lines.push({ line: sig.assign.line, from: sig.assign.col + 2 });
        for (let i = sig.assign.line + 1; i < d.end; i++) lines.push({ line: i, from: 0 });
        out.push({ decl: d, lines, isLemma: d.kind === 'lemma' || d.kind === 'theorem' });
    }
    return out;
}

// ---------------------------------------------------------------------------------------------------------------
// indentation

export function indentRules(ctx) {
    const { P } = ctx;
    let prev = -1;
    let prevLine = -1;
    for (let i = 0; i < P.code.length; i++) {
        const ind = P.indent[i];
        if (ind < 0) continue;
        const inBrackets = P.stackAtLineStart[i].length > 0;
        if (ind % 2 === 1 && !inBrackets) {
            ctx.warn('indent-odd', i + 1, ind + 1, `indentation of ${ind} spaces is not a multiple of 2`);
        } else if (prev >= 0 && ind > prev + 2 && !inBrackets && !continuesTerm(P, prevLine)) {
            ctx.warn('indent-deep', i + 1, ind + 1, `indented ${ind - prev} spaces deeper than the line above; indent by 2`);
        }
        prev = ind;
        prevLine = i;
    }
}

/** the previous line ends with an operator / `:=` / `=>` etc. so the next line is a term continuation */
function continuesTerm(P, i) {
    const t = P.code[i].trimEnd();
    return /(:=|=>|↦|\bfun\b.*|[,+\-*/=<>≤≥≠∧∨↔→←$|^•∘]|\bthen|\belse|\bby|\bfrom|\bat|\bwith|\bcalc|\bdo)$/.test(t);
}

// ---------------------------------------------------------------------------------------------------------------
// proof body

const BINOPS = [':', '+', '-', '*', '/', '=', '≠', '>', '<', '≥', '≤'];
const NOT_BINOP = /^(:=|<;>|<\||<->|<-|<;|=>|->|>>|\*>|\*\]|\*,|\*\)|-\/|-\]|-,|-⟩|\/\\|<>|<\$>|<\*>)/;

export function proofRules(ctx) {
    const { P } = ctx;
    for (const b of bodies(ctx)) {
        const d = b.decl;
        const proofStart = d.markers.proof != null && d.markers.proof > d.sig.assign.line ? d.markers.proof + 1 : d.sig.assign.line + 1;

        // binary operators at the start of a continuation line (proof only)
        if (b.isLemma) {
            for (let i = proofStart; i < d.end; i++) {
                const t = P.code[i].trim();
                if (!t || NOT_BINOP.test(t)) continue;
                const op = BINOPS.find((o) => t.startsWith(o));
                if (!op) continue;
                if (op === '-' && /^-\s*[⟩,|)]/.test(t)) continue; // rintro / rcases clear pattern
                const pk = prevCode(P, i);
                if (op === '-' && pk < i && /([=≠<>≤≥+\-*/(\[,:]|:=|=>|↦)\s*$/.test(P.code[pk])) continue; // unary minus
                if (op === '<' && /^<\s*;/.test(t)) continue;
                ctx.warn('proof-binop-newline', i + 1, P.indent[i] + 1, `line starts with \`${op}\`: keep the binary operator on the previous line (no line break before \`${op}\`)`);
            }
        }

        for (const { line: i, from } of b.lines) {
            const l = P.code[i];
            const seg = l.slice(from);
            if (!seg.trim()) continue;
            tokenRules(ctx, d, i, from);
        }
        bulletRule(ctx, d, b.lines);
        if (!ctx.astCovered.has('have-inline-once')) haveOnceRule(ctx, d, b.lines);
        holeRule(ctx, d, b.lines);
    }
}

function tokenRules(ctx, d, i, from) {
    const { P } = ctx;
    const l = P.code[i];
    const init = P.stackAtLineStart[i];
    const stackAt = [];
    walk(l, (ch, j, depth, top) => { stackAt[j] = top; }, init);
    const at = (re, cb) => {
        re.lastIndex = from;
        let m;
        while ((m = re.exec(l))) {
            if (m.index < from) continue;
            cb(m);
        }
    };
    const nextCode = () => {
        for (let k = i + 1; k < d.end; k++) if (P.code[k].trim()) return k;
        return -1;
    };

    // rcases → obtain (not `rcases h : e with …`, not several targets)
    at(/(?<![\w.'])rcases\b(?!\?)/g, (m) => {
        const rest = l.slice(m.index + 6);
        const target = rest.split(/\bwith\b/)[0];
        if (/^\s*\w[\w'.]*\s*:(?!=)/.test(rest)) return;
        if (walk(target, (ch, j, depth) => depth === 0 && ch === ',') >= 0) return;
        ctx.warn('tactic-rcases', i + 1, m.index + 1, 'use `obtain ⟨…⟩ := h` instead of `rcases h with ⟨…⟩`');
    });
    // by_cases (not followed by `<;>`) → if … then … else …
    at(/(?<![\w.'])by_cases\b/g, (m) => {
        if (/<;>/.test(l.slice(m.index))) return;
        const k = nextCode();
        if (k >= 0 && /^\s*<;>/.test(P.code[k])) return;
        ctx.warn('tactic-by-cases', i + 1, m.index + 1, 'use `if h : p then … else …` instead of `by_cases h : p`');
    });
    // AST versions (parser flag `inst` on Lean_have / Lean_let) run when the file parses
    if (!ctx.astCovered.has('tactic-haveI')) at(/(?<![\w.'])haveI\b/g, (m) => ctx.warn('tactic-haveI', i + 1, m.index + 1, 'use `have` instead of `haveI`'));
    if (!ctx.astCovered.has('tactic-letI')) at(/(?<![\w.'])letI\b/g, (m) => ctx.warn('tactic-letI', i + 1, m.index + 1, 'use `let` instead of `letI`'));

    // calc
    at(/(?<![\w.'])calc\b/g, (m) => {
        const before = l.slice(0, m.index);
        let prevBy = /(?<![\w.'])by\s*$/.test(before);
        if (!prevBy && !before.trim()) {
            // `by` at the end of the previous code line
            for (let k = i - 1; k >= 0; k--) {
                if (!P.code[k].trim()) continue;
                prevBy = /(?<![\w.'])by\s*$/.test(P.code[k]);
                break;
            }
        }
        if (prevBy) ctx.warn('by-calc', i + 1, m.index + 1, 'use `calc` directly instead of `by calc`');
        const top = stackAt[m.index];
        if (top === '(' || top === '[') {
            ctx.warn('calc-in-brackets', i + 1, m.index + 1, top === '[' ? '`calc` inside the `[…]` of rw/erw/simp: prove it with a separate step' : '`calc` inside `(…)` as an argument: prove it with a separate step');
        }
        let first = l.slice(m.index + 4).trim();
        if (!first) {
            const k = nextCode();
            first = k >= 0 ? P.code[k].trim() : '_';
        }
        if (!first.startsWith('_')) ctx.warn('calc-start-underscore', i + 1, m.index + 1, 'start the `calc` chain with `_` (e.g. `calc _ = b := …`), not with the left-hand side');
    });

    // `(by …)`: one-liner, and with a type ascription no `;`
    at(/\(\s*by\b/g, (m) => {
        const close = closerOf(P, i, m.index);
        if (!close) return;
        if (close.line !== i) {
            ctx.warn('paren-by-multiline', i + 1, m.index + 1, 'multi-line tactic block inside `(by …)`: make it a one-liner or prove it in a separate `have`/step');
            return;
        }
        const inner = l.slice(m.index + 1, close.col);
        let colon = false;
        let semi = false;
        walk(inner, (ch, j, depth) => {
            if (depth !== 0) return;
            if (ch === ':' && inner[j + 1] !== '=' && inner[j - 1] !== ':') colon = true;
            if (ch === ';' && inner[j - 1] !== '<') semi = true;
        });
        if (colon && semi) ctx.warn('paren-by-semicolon', i + 1, m.index + 1, '`(by tac₁; tac₂ : T)`: the type-ascribed `by` term must be a single tactic, no `;`');
    });

    at(/(?<![\w.'])from\s+by\b/g, (m) => ctx.warn('from-by', i + 1, m.index + 1, '`show T from by tac` → `show T by tac` (or `show T from e`)'));

    // `by exact e` → `e` (when the `by` block is exactly `exact e`)
    at(/(?<![\w.'])by\s+exact\b/g, (m) => {
        const top = stackAt[m.index];
        let rest = l.slice(m.index);
        if (top) {
            // the `by` block ends at the closer of the enclosing bracket (or a `,` at its level)
            let depth = 0;
            for (let j = 0; j < rest.length; j++) {
                const ch = rest[j];
                if ('([{⟨'.includes(ch)) depth++;
                else if (')]}⟩'.includes(ch)) { if (depth === 0) { rest = rest.slice(0, j); break; } depth--; }
                else if (depth === 0 && ch === ',') { rest = rest.slice(0, j); break; }
            }
        } else {
            const k = nextCode();
            if (k >= 0 && P.indent[k] > P.indent[i]) return; // the by block continues on the next lines
        }
        if (/;/.test(rest)) return;
        ctx.warn('by-exact', i + 1, m.index + 1, '`by exact e` → `e`');
    });

    // `?_` / `?x` holes: see `holeRule`
}

const escapeRe = (s) => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');

// After `·`: a branch with more than one step starts on a new line.
function bulletRule(ctx, d, lines) {
    const { P } = ctx;
    for (const { line: i, from } of lines) {
        const l = P.code[i];
        const m = /^(\s*)([·.])\s+(\S.*)$/.exec(l);
        if (!m || from > m[1].length) continue;
        if (m[2] === '.' && !/^\.\s/.test(l.trimStart())) continue;
        const bi = m[1].length;
        const content = m[3];
        let multi = false;
        walk(content, (ch, j, depth) => {
            if (depth === 0 && ch === ';' && content[j - 1] !== '<') multi = true;
        }, []);
        if (!multi) {
            // a further step of this branch: a following line at the branch's step indentation (bullet + 2)
            const base = P.stackAtLineStart[i].length;
            for (let k = i + 1; k < d.end; k++) {
                const ind = P.indent[k];
                if (ind < 0) continue;
                if (ind <= bi) break;
                if (ind === bi + 2 && P.stackAtLineStart[k].length === base && !/^\s*(<;>|\|)/.test(P.code[k]) && !continuesTerm(P, prevCode(P, k))) { multi = true; break; }
            }
        }
        if (multi) ctx.warn('bullet-newline', i + 1, bi + 1, `this \`${m[2]}\` branch has more than one step: put \`${m[2]}\` alone on its line and the steps below it`);
    }
}

function prevCode(P, k) {
    for (let j = k - 1; j >= 0; j--) if (P.indent[j] >= 0) return j;
    return k;
}

// `have h : T := …` referenced exactly once, by the very next `exact` / `apply` step: inline it.
function haveOnceRule(ctx, d, lines) {
    const { P } = ctx;
    const first = lines[0]?.line ?? d.end;
    for (let i = first; i < d.end; i++) {
        const m = /^(\s*)have\s+([\p{L}_][\p{L}\p{N}_'₀-₉]*)\s*(:(?!=)|:=)/u.exec(P.code[i]);
        if (!m || m[2] === 'this') continue;
        const ind = m[1].length;
        const name = m[2];
        // end of the have statement / next statement at the same indentation
        let k = i + 1;
        while (k < d.end && (P.indent[k] < 0 || P.indent[k] > ind || P.stackAtLineStart[k].length > P.stackAtLineStart[i].length)) k++;
        if (k >= d.end || P.indent[k] !== ind) continue;
        const next = k;
        // the next statement's extent
        let e = next + 1;
        while (e < d.end && (P.indent[e] < 0 || P.indent[e] > ind)) e++;
        // rest of the block (until dedent below `ind`), stopping at a re-definition of the name
        let total = 0;
        let blockEnd = next;
        for (let j = next; j < d.end; j++) {
            if (P.indent[j] >= 0 && P.indent[j] < ind) break;
            if (j > next && new RegExp(`^\\s*(have|let|obtain|intro|rintro|set)\\b.*(?<![\\p{L}\\p{N}_'.])${escapeRe(name)}(?![\\p{L}\\p{N}_'])`, 'u').test(P.code[j])) break;
            total += countWord(P.code[j], name);
            blockEnd = j;
        }
        void blockEnd;
        let inNext = 0;
        for (let j = next; j < e; j++) inNext += countWord(P.code[j], name);
        if (total !== 1 || inNext !== 1) continue;
        const nt = P.code[next].trim();
        if (!/^(exact|apply)\b/.test(nt)) continue;
        if (/\bat\b/.test(nt)) continue;
        ctx.warn('have-inline-once', i + 1, ind + 1, `\`${name}\` is used only once, by the next \`${nt.split(/\s/)[0]}\`: inline it (e.g. \`apply\` with a hole \`_\` and prove it afterwards) instead of a \`have\``);
    }
}

// ---------------------------------------------------------------------------------------------------------------
// holes: `?_` / `?x`

const OPENERS = '([{⟨⦃';
const CLOSERS = ')]}⟩⦄';
/** tactics where `?_` is needed: their term's new goals are collected with natural holes disallowed */
const NEEDS_SYNTHETIC = new Set(['refine', "refine'", 'have', 'haveI', 'let', 'letI', 'suffices', 'show', 'calc']);
/** tactics where an unassigned `_` becomes a new goal just like `?_` (or `?_` is an error anyway: `exact`) */
const UNDERSCORE_OK = new Set(['apply', 'exact', 'exacts', 'rw', 'rwa', 'erw', 'rewrite', 'nth_rewrite', 'nth_rw', 'simp_rw', 'simp', 'simpa', 'convert', 'linarith', 'nlinarith', 'positivity', 'field_simp', 'norm_num', 'grind', 'aesop']);
const HEADS = new Set([...NEEDS_SYNTHETIC, ...UNDERSCORE_OK, 'obtain', 'rcases', 'use', 'exists', 'specialize', 'intro', 'rintro', 'cases', 'induction', 'match', 'case', 'next', 'constructor', 'filter_upwards', 'gcongr', 'congr', 'trans', 'set', 'change', 'unfold', 'omega', 'conv', 'ext', 'funext', 'by_contra', 'push_neg', 'lift', 'wlog', 'choose', 'generalize', 'subst', 'symm', 'on_goal', 'all_goals', 'any_goals', 'first', 'try', 'repeat', 'iterate', 'focus', 'split', 'split_ifs', 'left', 'right', 'contrapose', 'exact_mod_cast', 'apply_fun']);

/**
 * The tactic a hole at `pos` of `text` (the joined declaration body) belongs to:
 * scan backwards, ignoring sibling elements (after a `,` of the same bracket level) and stopping at statement ends.
 * Returns a tactic name, 'alt' (right-hand side of a `| pat => ?_` alternative) or null (unknown).
 */
function holeHead(P, text, starts, pos) {
    let depth = 0;
    let skip = false;
    let sawArrow = false;
    let line = starts.findLastIndex((s) => s <= pos);
    for (let k = pos - 1; k >= 0; k--) {
        const ch = text[k];
        if (ch === '\n') {
            // leaving line `line` upwards: only into a continuation (inside brackets, or deeper than the line above)
            const L = starts.lineNo[line];
            let up = line - 1;
            while (up >= 0 && P.indent[starts.lineNo[up]] < 0) up--;
            if (up < 0) return null;
            const U = starts.lineNo[up];
            if (!(P.stackAtLineStart[L].length > 0 || P.indent[L] > P.indent[U])) return null;
            line = up;
            k = starts[up] + P.code[U].length;
            continue;
        }
        if (CLOSERS.includes(ch)) { depth++; continue; }
        if (OPENERS.includes(ch)) { if (depth > 0) depth--; else skip = false; continue; }
        if (depth > 0) continue;
        if (ch === ';' && text[k - 1] !== '<') return null;
        if (ch === ',') { skip = true; continue; }
        if (ch === '>' && text[k - 1] === '=') sawArrow = true;
        if (ch === '|' && text[k + 1] !== '>' && text[k - 1] !== '<') {
            const before = text.slice(starts[line], k).trimEnd();
            if (sawArrow && !skip && (before.trim() === '' || /\b(with|fun|match)$/.test(before))) return 'alt';
            continue;
        }
        if (skip) continue;
        if (/[\p{L}_']/u.test(ch) && !/[\p{L}\p{N}_'.!?]/u.test(text[k - 1] ?? ' ')) {
            const w = /^[\p{L}_][\p{L}\p{N}_'!?]*/u.exec(text.slice(k))[0];
            if (HEADS.has(w)) return w;
        }
    }
    return null;
}

export function holeRule(ctx, d, lines) {
    const { P } = ctx;
    if (!lines.length) return;
    // join the body; `starts[i]` = offset of body line i in `text`, `starts.lineNo[i]` = its file line
    const starts = [];
    starts.lineNo = [];
    let text = '';
    const first = lines[0].line;
    for (let i = first; i < d.end; i++) {
        starts.push(text.length);
        starts.lineNo.push(i);
        text += (i === first ? ' '.repeat(lines[0].from) + P.code[i].slice(lines[0].from) : P.code[i]) + '\n';
    }
    const re = /\?(_(?![\p{L}\p{N}_'])|[\p{L}_][\p{L}\p{N}_'₀-₉]*)/gu;
    let m;
    while ((m = re.exec(text))) {
        const c = text[m.index - 1];
        if (c && /[\p{L}\p{N}_'!?)\]⟩}]/u.test(c)) continue; // `exact?`, `x?_`, `get?` …: not a hole
        const bi = starts.findLastIndex((s) => s <= m.index);
        const line = starts.lineNo[bi] + 1;
        const col = m.index - starts[bi] + 1;
        if (m[1] !== '_') {
            ctx.warn('hole-question', line, col, `named hole \`?${m[1]}\`: use \`_\` (or \`?_\` inside \`refine\`)`, { hole: 'named' });
            continue;
        }
        const head = holeHead(P, text, starts, m.index);
        if (head && UNDERSCORE_OK.has(head)) {
            ctx.warn('hole-question', line, col, head.startsWith('exact') ? `\`?_\` in \`${head}\`, which cannot leave new goals: use \`apply\` with \`_\` (or \`refine\` with \`?_\`)` : `\`?_\` in \`${head}\`: use \`_\` (an unassigned \`_\` becomes a new goal)`, { hole: head });
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// `_identifier` binders / holes → `_`

export function underscoreNameRule(ctx) {
    const { P } = ctx;
    for (const d of ctx.decls) {
        const from = d.attrLine >= 0 ? d.attrLine : d.line;
        const seen = new Set();
        // occurrences of `name` that are uses, not binding sites (`name :`, or in an intro / fun / pattern binder list)
        const uses = (name) => {
            let n = 0;
            for (let i = from; i < d.end; i++) {
                const l = P.code[i];
                let k = -1;
                while ((k = l.indexOf(name, k + 1)) >= 0) {
                    const before = l[k - 1];
                    const after = l[k + name.length];
                    if ((before && /[\p{L}\p{N}_'.!?]/u.test(before)) || (after && /[\p{L}\p{N}_'!?₀-₉]/u.test(after))) continue;
                    if (/^\s*:(?!=)/.test(l.slice(k + name.length))) continue;
                    if (/(^|[^\p{L}\p{N}_'])((intro|rintro|fun|obtain|rcases|cases|induction|with)\b|[λ∑∏∫∀∃⨆⨅])[^,;]*$/u.test(l.slice(0, k)) && !/[[(]\s*$/.test(l.slice(0, k).replace(/^.*\b(intro|rintro|fun|λ)\b/u, ''))) continue;
                    n++;
                }
            }
            return n;
        };
        for (let i = from; i < d.end; i++) {
            const l = P.code[i];
            const re = /(^|[\s(⟨[{,])(_[\p{L}][\p{L}\p{N}_'!?₀-₉]*)/gu;
            let m;
            while ((m = re.exec(l))) {
                const name = m[2];
                const at = m.index + m[1].length;
                re.lastIndex = at + name.length;
                if (name === '_root_' || seen.has(name)) continue;
                if (/^\[\s*$/.test(m[1]) && /^\s*[<∈]/.test(l.slice(at + name.length))) continue; // tensor binder `[_i < n]`
                if (l[at + name.length] === '.') continue; // `_foo.bar`: a namespace path, not a binder
                seen.add(name);
                const plain = name.slice(1);
                ctx.warn('binder-underscore-name', i + 1, at + 1,
                    uses(name) > 0 ? `\`${name}\` is referenced: name it \`${plain}\` (use \`_\` only where it is unused)` : `\`${name}\`: use \`_\` for an unused binder / unnamed hole`);
            }
        }
    }
}
