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
        if (b.isLemma) termModeExactRule(ctx, d);
        if (!ctx.astCovered.has('have-inline-once')) haveOnceRule(ctx, d, b.lines);
        holeRule(ctx, d, b.lines);
        rwExactRule(ctx, d);
        showMultilineRule(ctx, d);
    }
    jointRandomSymbolRule(ctx);
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

/**
 * `term-mode-exact`: the whole proof is a single `exact e` — `… := by exact e`, or `… := by` / `-- proof` / `  exact e`
 * (blank / comment lines in between; `e` may continue on deeper lines) — so it should be the term itself:
 * `… :=` / `-- proof` / `  e` (Lemma/Random/Measurable_R.lean). Not when the block has another tactic (a further line
 * at the tactic's indentation), `;` / `<;>` at the top level, or a `·` / `<;>` continuation line; not `exact?` / `exacts`.
 * Records the proof's line range in `ctx.termModeExact`: `lintLean` drops the `apply`-instead-of-`exact` hints there.
 */
function termModeExactRule(ctx, d) {
    const { P } = ctx;
    const a = d.sig?.assign;
    if (!a) return;
    const tail = P.code[a.line].slice(a.col + 2);
    const m = /^(\s*)by(?![\p{L}\p{N}_'!?.])(\s*)(.*)$/u.exec(tail);
    if (!m) return;
    const byCol = a.col + 2 + m[1].length;
    let exLine = a.line;
    let exCol = byCol + 2 + m[2].length;
    let tacCol = P.indent[a.line]; // one-line `:= by exact e`: every later line of the declaration continues `e`
    if (!m[3].trim()) {
        exLine = -1;
        for (let k = a.line + 1; k < d.end; k++) if (P.indent[k] >= 0) { exLine = k; break; }
        if (exLine < 0) return;
        exCol = P.indent[exLine];
        tacCol = exCol; // a later line at (or left of) the `exact` column would be a second tactic
    }
    const first = P.code[exLine].slice(exCol);
    const em = /^exact(?![\p{L}\p{N}_'!?.])\s*/u.exec(first);
    if (!em || !first.slice(em[0].length).trim()) return;
    let last = exLine;
    const parts = [first];
    for (let k = exLine + 1; k < d.end; k++) {
        if (P.indent[k] < 0) continue;
        if (P.indent[k] <= tacCol) return;
        if (/^\s*(<;>|·)/.test(P.code[k])) return;
        parts.push(P.code[k]);
        last = k;
    }
    let combined = false;
    walk(parts.join('\n'), (ch, j, depth) => {
        if (depth === 0 && ch === ';') combined = true; // `tac; tac` and `tac <;> tac`
    }, []);
    if (combined) return;
    // the term as written (raw source), for the message
    const at = exCol + em[0].length;
    const rawFirst = P.raw[exLine].slice(at, at + P.code[exLine].slice(at).trimEnd().length); // no trailing comment
    let term = rawFirst.length > 60 ? rawFirst.slice(0, 59) + '…' : rawFirst;
    if (last > exLine && !term.endsWith('…')) term += ' …';
    (ctx.termModeExact ??= []).push({ from: a.line, to: last, byLine: a.line, byCol });
    ctx.warn('term-mode-exact', a.line + 1, byCol + 1,
        `the proof is a single \`exact\`: use term mode — \`… :=\` (no \`by\`) / \`-- proof\` / \`  ${term}\` (the term without \`exact\`, 2-indented, as in Lemma/Random/Measurable_R.lean); this takes precedence over "prefer \`apply\` instead of \`exact\`"`);
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


// ---------------------------------------------------------------------------------------------------------------
// `rw` followed by `exact`, multi-line `show … by/from` in `rw`/`apply`, `JointRandomSymbol` → flat tuple

const BR_OPEN = { '(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄', '⁅': '⁆' };
const BR_CLOSE = { ')': '(', ']': '[', '}': '{', '⟩': '⟨', '⦄': '⦃', '⁆': '⁅' };
const KW_PREV = /[\p{L}\p{N}_'!?₀-₉ₐ-ₜ.]/u;
const KW_NEXT = /[\p{L}\p{N}_'!?₀-₉ₐ-ₜ]/u;
const ATOM_RE = /^@?[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*(?:\.[ \t]*[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*)*$/u;

/** keyword at `i` (not a prefix/suffix of a longer name, and not `foo.kw`) */
function isKw(s, i, kw) {
    if (i < 0 || !s.startsWith(kw, i)) return false;
    const prev = s[i - 1];
    const next = s[i + kw.length];
    if (prev && KW_PREV.test(prev)) return false;
    if (next && KW_NEXT.test(next)) return false;
    return true;
}

function lineStartsOf(code) {
    const starts = [0];
    for (let i = 0; i < code.length - 1; i++) starts.push(starts[i] + code[i].length + 1);
    return starts;
}

function posAt(starts, idx) {
    let lo = 0;
    let hi = starts.length - 1;
    while (lo < hi) {
        const mid = (lo + hi + 1) >> 1;
        if (starts[mid] <= idx) lo = mid;
        else hi = mid - 1;
    }
    return { line: lo, col: idx - starts[lo] };
}

function matchBracket(s, openIdx) {
    const want = BR_OPEN[s[openIdx]];
    if (!want) return -1;
    let depth = 0;
    for (let i = openIdx; i < s.length; i++) {
        const ch = s[i];
        if (BR_OPEN[ch]) depth++;
        else if (BR_CLOSE[ch]) {
            depth--;
            if (depth === 0 && ch === want) return i;
        }
    }
    return -1;
}

function skipWsIdx(s, i) {
    while (i < s.length && /[ \t\n]/.test(s[i])) i++;
    return i;
}

/** `rw` / `rwa` / `erw` / `rewrite` sitting where a tactic can start (after a newline, `;`, `by`, `<;>`, `·`) */
function isTacticHead(s, i) {
    let k = i - 1;
    while (k >= 0 && (s[k] === ' ' || s[k] === '\t')) k--;
    if (k < 0 || s[k] === '\n' || s[k] === ';' || s[k] === '·' || s[k] === '|') return true;
    if (k >= 2 && s[k] === '>' && s[k - 1] === ';' && s[k - 2] === '<') return true;
    if (s[k] === 'y' && isKw(s, k - 1, 'by')) return true;
    return false;
}

function rewriteWord(s, i) {
    for (const w of ['rewrite', 'rwa', 'erw', 'rw']) if (isKw(s, i, w)) return w;
    return '';
}

/**
 * `[…]` of a rewrite tactic at `i` (the keyword), or null.
 * Optional config `(…)` is skipped only when a `[` follows it.
 */
function rewriteBracket(s, i, word, limit) {
    let j = skipWsIdx(s, i + word.length);
    if (j >= limit) return null;
    if (s[j] === '(') {
        const cl = matchBracket(s, j);
        if (cl < 0 || cl >= limit) return null;
        const after = skipWsIdx(s, cl + 1);
        if (after >= limit || s[after] !== '[') return null;
        j = after;
    }
    if (s[j] !== '[') return null;
    const cl = matchBracket(s, j);
    if (cl < 0 || cl > limit) return null;
    return { open: j, close: cl };
}

function hasCode(s) {
    return /\S/.test(s);
}

/**
 * `exact` whose argument is one atomic term: an identifier (`h₅`, `this`, `h'`, `h.symm`),
 * an `@`-prefixed name, or parentheses around just that. Not `exact by/show/fun/calc/…`,
 * not a second juxtaposed argument, not a proof term.
 * Returns the argument text, or null.
 */
function simpleExactArg(P, line, col) {
    const l = P.code[line] ?? '';
    if (!isKw(l, col, 'exact')) return null;
    let c = col + 'exact'.length;
    while (c < l.length && /[ \t]/.test(l[c])) c++;
    if (c >= l.length) return null;
    const ch = l[c];
    if (BR_OPEN[ch]) {
        const cl = closerOf(P, line, c);
        if (!cl || cl.line !== line) return null;
        const inner = l.slice(c + 1, cl.col).trim();
        if (!ATOM_RE.test(inner)) return null;
        return inner;
    }
    const m = /^@?[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*(?:\.[ \t]*[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*)*/u.exec(l.slice(c));
    if (!m || m.index !== 0) return null;
    let k = c + m[0].length;
    while (k < l.length && /[ \t]/.test(l[k])) k++;
    if (k < l.length && /[\p{L}_@([]/u.test(l[k])) return null;
    return m[0];
}

/**
 * Next tactic after a rewrite's `[…]` (and an `at` clause), ignoring blank lines and comments
 * (already blanked). Same-line only through `;`. A later line counts only at the same indent
 * and the same bracket depth as the `rw` line — so `exact` inside the `[…]` is never "next".
 * `<;>` is not the `rwa` pattern.
 */
function exactAfterRewrite(P, rwLine, closeLine, closeCol, endLine) {
    const rwIndent = P.indent[rwLine];
    const base = P.stackAtLineStart[rwLine].length;
    const line0 = P.code[closeLine] ?? '';
    let c = closeCol + 1;
    while (c < line0.length && /[ \t]/.test(line0[c])) c++;
    if (line0.startsWith('<;>', c)) return null;
    if (isKw(line0, c, 'at')) {
        c += 2;
        while (c < line0.length && !line0.startsWith('<;>', c) && !(line0[c] === ';' && line0[c - 1] !== '<')) c++;
        if (line0.startsWith('<;>', c)) return null;
        if (line0[c] === ';') {
            c++;
            while (c < line0.length && /[ \t]/.test(line0[c])) c++;
            const arg = simpleExactArg(P, closeLine, c);
            return arg ? { line: closeLine, col: c, arg } : null;
        }
    } else if (line0[c] === ';' && line0[c - 1] !== '<') {
        c++;
        while (c < line0.length && /[ \t]/.test(line0[c])) c++;
        const arg = simpleExactArg(P, closeLine, c);
        return arg ? { line: closeLine, col: c, arg } : null;
    } else if (c < line0.length && /[\p{L}_]/u.test(line0.slice(c))) {
        return null;
    }
    let k = closeLine + 1;
    while (k < endLine && P.indent[k] < 0) k++;
    if (k < endLine && P.indent[k] >= rwIndent && /^\s*at(?![\p{L}\p{N}_'!?₀-₉ₐ-ₜ])/u.test(P.code[k])) {
        if (P.code[k].includes('<;>')) return null;
        k++;
        while (k < endLine && P.indent[k] < 0) k++;
    }
    if (k >= endLine || P.indent[k] !== rwIndent) return null;
    if (P.stackAtLineStart[k].length !== base) return null;
    if (/^\s*<;>/.test(P.code[k])) return null;
    const col = P.indent[k];
    const arg = simpleExactArg(P, k, col);
    return arg ? { line: k, col, arg } : null;
}

/**
 * `rw-exact`: `rw […]` (optional `at`) immediately followed by `exact <atom>` simplifies to `rwa`.
 * Not `rwa` / `erw` / `rewrite` (those are not spelled `rw`). Not `<;> exact`.
 */
function rwExactRule(ctx, d) {
    const { P } = ctx;
    const text = P.code.join('\n');
    const starts = lineStartsOf(P.code);
    const from = starts[d.line] ?? 0;
    const to = d.end < starts.length ? starts[d.end] : text.length;
    for (let i = from; i < to; i++) {
        if (!isKw(text, i, 'rw') || !isTacticHead(text, i)) continue;
        const br = rewriteBracket(text, i, 'rw', to);
        if (!br) continue;
        const rw = posAt(starts, i);
        const cl = posAt(starts, br.close);
        const ex = exactAfterRewrite(P, rw.line, cl.line, cl.col, d.end);
        if (ex) {
            ctx.warn(
                'rw-exact',
                rw.line + 1,
                rw.col + 1,
                `\`rw […]\` is immediately followed by \`exact ${ex.arg}\`: use \`rwa […]\` and drop the trailing \`exact\``,
            );
        }
    }
}

/**
 * End index (exclusive) of the tactic after `by` at bracket depth `depth`.
 * Stops before a closer that leaves `depth`, or before a top-level `,` (the next rewrite rule).
 */
function endOfByBlock(text, after, hi, depth) {
    let d = depth;
    for (let i = after; i < hi; i++) {
        const ch = text[i];
        if (BR_OPEN[ch]) d++;
        else if (BR_CLOSE[ch]) {
            d--;
            if (d < depth) return i;
        } else if (d === depth && ch === ',') return i;
    }
    return hi;
}

/**
 * The `by` / `from` that proves term-mode `show` (not a `by` nested in the type).
 * `depth` is the bracket depth of the `show` keyword.
 * Returns `{ kind: 'by'|'from', at, end }` where `end` is exclusive.
 */
function findShowProof(text, from, hi, depth) {
    let d = depth;
    for (let i = from; i < hi; i++) {
        const ch = text[i];
        if (BR_OPEN[ch]) { d++; continue; }
        if (BR_CLOSE[ch]) {
            d--;
            if (d < depth) return null;
            continue;
        }
        if (d !== depth) continue;
        if (ch === ',') return null;
        if (isKw(text, i, 'from')) return { kind: 'from', at: i, end: endOfByBlock(text, i + 4, hi, depth) };
        if (isKw(text, i, 'by')) return { kind: 'by', at: i, end: endOfByBlock(text, i + 2, hi, depth) };
    }
    return null;
}

function isMultilineShowProof(text, proof) {
    const kwLen = proof.kind === 'from' ? 4 : 2;
    const after = text.slice(proof.at + kwLen, proof.end);
    const nl = after.indexOf('\n');
    return nl >= 0 && hasCode(after.slice(nl + 1));
}

/** `apply` / `refine` / `exact` sitting where a tactic can start */
function applyLikeWord(s, i) {
    for (const w of ['apply', 'refine', 'exact']) if (isKw(s, i, w)) return w;
    return '';
}

/**
 * Argument span of `apply` / `refine` / `exact` at `wordIdx`.
 * Prefer a leading bracket group (then a same-line `.name` chain); otherwise stop at a
 * top-level newline / `;` / `·`.
 */
function hostArgRange(text, wordIdx, word, limit) {
    let i = skipWsIdx(text, wordIdx + word.length);
    if (i >= limit) return null;
    if (!BR_OPEN[text[i]]) {
        let depth = 0;
        for (let j = i; j < limit; j++) {
            const ch = text[j];
            if (BR_OPEN[ch]) depth++;
            else if (BR_CLOSE[ch]) {
                if (depth === 0) return { start: i, end: j };
                depth--;
            } else if (depth === 0 && (ch === ';' || ch === '·' || ch === '\n')) {
                return { start: i, end: j };
            }
        }
        return { start: i, end: limit };
    }
    const cl = matchBracket(text, i);
    if (cl < 0 || cl > limit) return null;
    let end = cl + 1;
    for (;;) {
        let k = end;
        while (k < limit && /[ \t]/.test(text[k])) k++;
        if (k >= limit || text[k] !== '.') break;
        k++;
        const m = /^[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*/u.exec(text.slice(k));
        if (!m) break;
        k += m[0].length;
        while (k < limit && /[ \t]/.test(text[k])) k++;
        while (k < limit && BR_OPEN[text[k]]) {
            const c2 = matchBracket(text, k);
            if (c2 < 0 || c2 > limit) break;
            k = c2 + 1;
            while (k < limit && /[ \t]/.test(text[k])) k++;
        }
        end = k;
    }
    return { start: i, end: Math.min(end, limit) };
}

/**
 * `show-multiline`.
 *
 * Multi-line `show TYPE by …` / `show TYPE from …` is not allowed as a tactic
 * argument of `rw` / `rwa` / `erw` / `rewrite`, or of `apply` / `refine` / `exact`.
 * Suggest `have h : TYPE := by …` then use `h` (any name).
 *
 * Why older checks missed In_Ico.lean:
 * - `paren-by-multiline` only matches a same-line `(by` and that parenthesis's closer.
 * - `rw-show-multiline` walked only rewrite `[…]` and treated `from` as "not a by-proof"
 *   (`findShowBy` returned null), so `rw [show … from funext … by⏎ …]` and
 *   `apply (… (show … by⏎ …))` never warned.
 *
 * One-line proofs (`rw [show T by exact h]`, `exact (show T by fun_prop)`, or a line
 * break only in the type) stay quiet. `refine` / `exact` share the same host-arg walk
 * as `apply` (same parenthesized `(show … by` bug); other tactics are out of scope.
 */

/** show is a rewrite-list element, not a show tactic inside the by block. */
function isRewriteElement(text, showIdx) {
    let k = showIdx - 1;
    while (k >= 0 && /\s/.test(text[k])) k--;
    if (k < 0) return false;
    if (text[k] === '[' || text[k] === ',' || text[k] === '\u2190') return true;
    if (text[k] === '-' && text[k - 1] === '<') return true;
    return false;
}

function showMultilineRule(ctx, d) {
    const { P } = ctx;
    const text = P.code.join('\n');
    const starts = lineStartsOf(P.code);
    const from = starts[d.line] ?? 0;
    const to = d.end < starts.length ? starts[d.end] : text.length;

    /** @type {{ start: number, end: number, label: string, rewrite: boolean }[]} */
    const hosts = [];
    for (let i = from; i < to; i++) {
        const word = rewriteWord(text, i);
        if (!word || !isTacticHead(text, i)) continue;
        const br = rewriteBracket(text, i, word, to);
        if (!br) continue;
        const label = word === 'erw' ? 'erw' : 'rw';
        hosts.push({ start: br.open + 1, end: br.close, label, rewrite: true });
        i = br.close;
    }
    for (let i = from; i < to; i++) {
        const word = applyLikeWord(text, i);
        if (!word || !isTacticHead(text, i)) continue;
        const range = hostArgRange(text, i, word, to);
        if (!range) continue;
        hosts.push({ start: range.start, end: range.end, label: word, rewrite: false });
        i = Math.max(i, range.end - 1);
    }

    const seen = new Set();
    for (const host of hosts) {
        let depth = 0;
        for (let j = host.start; j < host.end; j++) {
            const ch = text[j];
            if (BR_OPEN[ch]) { depth++; continue; }
            if (BR_CLOSE[ch]) { depth--; continue; }
            if (!isKw(text, j, 'show')) continue;
            if (seen.has(j)) continue;
            if (host.rewrite) {
                if (depth !== 0 || !isRewriteElement(text, j)) continue;
            } else if (isTacticHead(text, j)) {
                continue;
            }
            const found = findShowProof(text, j + 4, host.end, depth);
            if (!found || !isMultilineShowProof(text, found)) continue;
            seen.add(j);
            let typeText = text.slice(j + 4, found.at).replace(/\s+/g, ' ').trim();
            if (typeText.length > 80) typeText = `${typeText.slice(0, 77)}…`;
            const at = posAt(starts, found.at);
            const where = host.rewrite
                ? `${host.label} [show … ${found.kind} …]`
                : `${host.label} (… show … ${found.kind} …)`;
            const use = host.rewrite ? `${host.label} [h]` : host.label;
            ctx.warn(
                'show-multiline',
                at.line + 1,
                at.col + 1,
                `multi-line \`${found.kind}\` inside \`${where}\`: pull the proof out (\`have h : ${typeText} := by\` … then use \`h\` in the \`${use}\`; any name, not only \`this\`)`,
            );
            j = found.at;
        }
    }
}

function skipModifiers(s, i) {
    for (;;) {
        i = skipWsIdx(s, i);
        const ch = s[i];
        if (ch !== '(' && ch !== '{' && ch !== '⦃') return i;
        const cl = matchBracket(s, i);
        if (cl < 0) return i;
        const inner = s.slice(i + 1, cl);
        const named = /^\s*[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*\s*:=/u.test(inner);
        if (ch === '⦃' || named) { i = cl + 1; continue; }
        return i;
    }
}

/** one juxtaposition argument: a bracket group, or a dotted name (not the following applied arguments) */
function parseAtomStr(s, i) {
    i = skipWsIdx(s, i);
    if (i >= s.length) return null;
    const ch = s[i];
    if (BR_OPEN[ch]) {
        const cl = matchBracket(s, i);
        if (cl < 0) return null;
        return { text: s.slice(i, cl + 1), end: cl + 1 };
    }
    const m = /^@?[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*(?:\.[ \t]*[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*)*/u.exec(s.slice(i));
    if (!m || m.index !== 0) return null;
    return { text: m[0], end: i + m[0].length };
}

function stripWrappingParens(s) {
    let t = s.trim();
    for (;;) {
        if (!t.startsWith('(')) break;
        const cl = matchBracket(t, 0);
        if (cl !== t.length - 1) break;
        t = t.slice(1, -1).trim();
    }
    return t;
}

/** two term arguments after a `JointRandomSymbol` head, or null (bare / partial / not a call) */
function parseJrsArgs(s, i) {
    const a0 = skipModifiers(s, i);
    const a = parseAtomStr(s, a0);
    if (!a || skipModifiers(s, a0) !== a0) return null;
    const b0 = skipModifiers(s, a.end);
    const b = parseAtomStr(s, b0);
    if (!b || skipModifiers(s, b0) !== b0) return null;
    return [a.text, b.text];
}

function jrsComponents(text) {
    const t = stripWrappingParens(text);
    if (!isKw(t, 0, 'JointRandomSymbol')) return [t];
    const args = parseJrsArgs(t, 'JointRandomSymbol'.length);
    if (!args) return [t];
    return [...jrsComponents(args[0]), ...jrsComponents(args[1])];
}

/**
 * `joint-random-symbol`: every occurrence, not only an argument of `MeasurableSpace.comap`
 * / `comap_measurable`. A nested spine on either side flattens into one product tuple:
 * `JointRandomSymbol x (JointRandomSymbol a b)` → `(x, a, b)`. Only a real application (two arguments) warns — a bare name such as `simp [JointRandomSymbol]` does not.
 */
function jointRandomSymbolRule(ctx) {
    const { P } = ctx;
    const text = P.code.join('\n');
    const starts = lineStartsOf(P.code);
    const kw = 'JointRandomSymbol';
    for (let i = 0; i <= text.length - kw.length; i++) {
        if (!isKw(text, i, kw)) continue;
        const at = posAt(starts, i);
        const args = parseJrsArgs(text, i + kw.length);
        if (!args) { i += kw.length - 1; continue; }
            const sug = `(${[...jrsComponents(args[0]), ...jrsComponents(args[1])].join(', ')})`;
            const shown = sug.length > 180 ? `${sug.slice(0, 177)}…` : sug;
            ctx.warn(
                'joint-random-symbol',
                at.line + 1,
                at.col + 1,
                `\`JointRandomSymbol\` → \`${shown}\` (any occurrence; a nested spine on either side flattens into one tuple)`,
            );
        i += kw.length - 1;
    }
}
