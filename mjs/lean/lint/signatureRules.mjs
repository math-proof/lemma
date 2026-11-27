/**
 * Signature rules of a lemma / theorem: binder lines before `-- given`, default arguments, combining binders,
 * `-- given` / `-- imply` / `-- proof` sections.
 */
import fs from 'node:fs';
import path from 'node:path';
import { parseSignature, hasWord, isBinderKeywordContext, isIdentChar } from './scan.mjs';

const REL = /[=≠<>≤≥∈∉⊆⊂⊇⊃∣↔∧∨¬≈≡]|∀|∃|\bTrue\b|\bFalse\b/;
const isLemma = (d) => d.kind === 'lemma' || d.kind === 'theorem';
/** Legacy `@[main, …]` attribute list (docstring / older path attrs). */
const isAttrMain = (d) => /^@\[\s*main\b/.test(d.attrs || '');
/**
 * Lemmas that use section markers (`-- imply` / `-- proof`, or `@[path] private lemma main`).
 * On Lemma/ files every `private lemma` also needs them. `-- given` is required only when an
 * explicit binder (hypothesis or given-section expression) belongs under it; omit `-- given`
 * when there are none. An empty `-- given` is deleted, not kept as a blank marker.
 */
function needsSectionMarkers(d, ctx) {
    const attrs = d.attrs || '';
    if (d.name === 'main' && (/\bpath\b/.test(attrs) || isAttrMain(d))) return true;
    if (isAttrMain(d)) return true;
    // Lemma/ private helpers: always `-- imply` / `-- proof` (standing Body rule via Random)
    if (ctx.isLemmaFile && d.kind === 'lemma' && /\bprivate\b/.test(ctx.P.code[d.line] ?? '')) return true;
    const { given, imply, proof } = d.markers || {};
    return given != null || imply != null || proof != null;
}

/** Explicit binders that belong under `-- given` (hypotheses and expression binders, not `{…}` / `[…]`). */
function explicitGivenBinders(groups) {
    return groups.filter((g) => g.kind === 'explicit');
}

/** First line/col that ends the `-- given` region: `-- imply`, else `:` / `:=` / `-- proof`. */
function givenRegionEnd(d, sig) {
    const { given, imply, proof } = d.markers;
    const stops = [];
    if (imply != null && imply > given) stops.push({ line: imply, col: 0 });
    if (imply == null) {
        if (sig.colon && sig.colon.line > given) stops.push(sig.colon);
        if (sig.assign && sig.assign.line > given) stops.push(sig.assign);
        if (proof != null && proof > given) stops.push({ line: proof, col: 0 });
    }
    if (!stops.length) return { line: d.end, col: 0 };
    stops.sort((a, b) => a.line - b.line || a.col - b.col);
    return stops[0];
}

/** No binder or other non-comment code between `-- given` and the next section. */
function givenRegionBlank(P, givenLine, end) {
    let text = '';
    const last = Math.min(end.line, P.code.length);
    for (let i = givenLine + 1; i < last; i++) text += (P.code[i] ?? '') + '\n';
    if (end.col > 0 && end.line > givenLine && end.line < P.code.length)
        text += P.code[end.line].slice(0, end.col);
    return !text.trim();
}

/** Heads such as `Measurable` / `IsVaR` (a proposition), not a data type. */
const PREDICATE_HEAD = /^(Is[A-Z]|Has[A-Z]|Odd$|Even$|Prime$|Nat\.Prime$|Squarefree$|Irreducible$|Continuous|Differentiable|Monotone|Antitone|StrictMono|StrictAnti|Injective$|Surjective$|Bijective$|Function\.|Measurable|AEMeasurable|Integrable|Summable|HasSum|Tendsto$|Filter\.Tendsto$|Nonempty$|Set\.Nonempty$|Finite$|Infinite$|Countable$|Bounded|BddAbove$|BddBelow$|Coprime$|Nat\.Coprime$|Disjoint$|Pairwise$|Antisymm|Symmetric$|Transitive$|Reflexive$|Convex|Concave|Fact$|Decidable$|Subsingleton$|Unique$|True$|False$)/;

/** `class Name … : Prop` declared under `Class/` (cached). `SinglePSpace` is one of these. */
let propClassCache = null;

function collectPropClasses(src, set) {
    const text = String(src || '').replace(/\/-[\s\S]*?-\//g, '').replace(/--[^\n]*/g, '');
    const re = /(?:^|\n)\s*(?:(?:noncomputable|private|protected|scoped|unsafe|partial)\s+)*class\s+([A-Za-z_][\w']*)/g;
    let m;
    while ((m = re.exec(text))) {
        let i = re.lastIndex;
        let depth = 0;
        let sort = '';
        for (; i < text.length; i++) {
            const c = text[i];
            if ('([{⟨'.includes(c)) depth++;
            else if (')]}⟩'.includes(c)) depth = Math.max(0, depth - 1);
            else if (depth === 0 && (text.startsWith('where', i) || (c === ':' && text[i + 1] === '='))) break;
            else if (depth === 0 && c === ':') {
                let j = i + 1;
                while (j < text.length && /\s/.test(text[j])) j++;
                sort = (/^[\w.]+/.exec(text.slice(j)) || [''])[0];
                break;
            }
        }
        if (sort === 'Prop') set.add(m[1]);
    }
}

function walkLeanFiles(dir, out) {
    let ents;
    try { ents = fs.readdirSync(dir, { withFileTypes: true }); } catch { return; }
    for (const ent of ents) {
        if (ent.name === 'v1' || ent.name === '.git' || ent.name === 'node_modules') continue;
        const p = path.join(dir, ent.name);
        if (ent.isDirectory()) walkLeanFiles(p, out);
        else if (ent.isFile() && ent.name.endsWith('.lean')) out.push(p);
    }
}

function propClassNames(root) {
    if (propClassCache) return propClassCache;
    const set = new Set();
    if (root) {
        const files = [];
        walkLeanFiles(path.join(root, 'Class'), files);
        for (const f of files) {
            try { collectPropClasses(fs.readFileSync(f, 'utf8'), set); } catch { /* unreadable */ }
        }
    }
    propClassCache = set;
    return set;
}

/** Type text is a proposition: a formula, a predicate head, or a `class … : Prop`. */
function isPropositionType(type, propClasses) {
    const t = String(type || '').trim();
    if (!t) return false;
    if (REL.test(t) || /\bProp\b/.test(t)) return true;
    const head = (/^[A-Za-z_][\w'.]*/.exec(t) || [''])[0];
    if (!head) return false;
    if (head === 'Prop' || PREDICATE_HEAD.test(head)) return true;
    const last = head.includes('.') ? head.slice(head.lastIndexOf('.') + 1) : head;
    return propClasses.has(head) || propClasses.has(last);
}

/** Head of `type` is a `class … : Prop` (instance search), not a ∀-wrapped or relational hypothesis. */
function isPropClassType(type, propClasses) {
    const t = String(type || '').trim();
    if (!t || /^(∀|Π|fun\b|λ)/.test(t)) return false;
    const head = (/^[A-Za-z_][\w'.]*/.exec(t) || [''])[0];
    if (!head) return false;
    const last = head.includes('.') ? head.slice(head.lastIndexOf('.') + 1) : head;
    return propClasses.has(head) || propClasses.has(last);
}

/** proposition-typed binder (relation / connective in its type) vs. a clear expression binder */
function propKind(g) {
    if (g.kind !== 'explicit' || !g.names.length) return null;
    const hyp = g.names.some((n) => /^_?h/.test(n));
    if (REL.test(g.type) || hyp) return 'prop';
    if (!/\bProp\b/.test(g.type)) return 'expr';
    return null;
}

const SUB_DIGIT = { '₀': 0, '₁': 1, '₂': 2, '₃': 3, '₄': 4, '₅': 5, '₆': 6, '₇': 7, '₈': 8, '₉': 9 };
const SUB_OF = Object.fromEntries(Object.entries(SUB_DIGIT).map(([s, i]) => [i, s]));

/** `h₀`…`h₉` or ASCII `h0`…`h9` → index; other names (incl. `hG`, `h10`) → null. */
function numberedHypIndex(name) {
    const m = /^h([₀₁₂₃₄₅₆₇₈₉])$/.exec(name) || /^h([0-9])$/.exec(name);
    if (!m) return null;
    return m[1] in SUB_DIGIT ? SUB_DIGIT[m[1]] : Number(m[1]);
}

function hypLabel(i, preferSub) {
    return preferSub ? `h${SUB_OF[i]}` : `h${i}`;
}

const BIND_KW = new Set(['∀', '∃', '∑', '∏', '⋂', '⋃', 'fun', 'λ']);
const ID_RE = /[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*/uy;

/** Identifiers of `type` that are not bound by `∀` / `∃` / `∑` / `∏` / `fun` / `λ` (text fallback). */
function freeNames(type, bound = new Set()) {
    const found = new Set();
    const text = String(type ?? '');
    let i = 0;
    const isId = (c) => c && /[\p{L}\p{N}_'!?₀-₉ₐ-ₜ]/u.test(c);
    while (i < text.length) {
        const ch = text[i];
        if (/\s/.test(ch)) { i++; continue; }
        let kw = '';
        if ('∀∃∑∏⋂⋃λ'.includes(ch)) kw = ch;
        else if (text.startsWith('fun', i) && !isId(text[i + 3])) kw = 'fun';
        if (kw && BIND_KW.has(kw)) {
            i += kw.length;
            const local = new Set();
            while (i < text.length) {
                while (i < text.length && /\s/.test(text[i])) i++;
                if (text.startsWith('=>', i) || text.startsWith('↦', i) || text[i] === ',' || text[i] === '∈' || text[i] === ':' || text[i] === '|') break;
                if (chOpen(text[i])) {
                    const close = CLOSE_OF[text[i]];
                    i++;
                    while (i < text.length && text[i] !== ':' && text[i] !== close) {
                        while (i < text.length && /\s/.test(text[i])) i++;
                        ID_RE.lastIndex = i;
                        const m = ID_RE.exec(text);
                        if (!m || m.index !== i) { if (i < text.length) i++; continue; }
                        local.add(m[0]);
                        i = ID_RE.lastIndex;
                    }
                    let depth = 1;
                    if (text[i] === ':') i++;
                    while (i < text.length && depth > 0) {
                        if (chOpen(text[i])) depth++;
                        else if (chClose(text[i])) depth--;
                        if (depth > 0) i++;
                    }
                    if (i < text.length && chClose(text[i])) i++;
                    continue;
                }
                ID_RE.lastIndex = i;
                const m = ID_RE.exec(text);
                if (m && m.index === i) { local.add(m[0]); i = ID_RE.lastIndex; continue; }
                break;
            }
            while (i < text.length && /\s/.test(text[i])) i++;
            if (text[i] === '∈' || text[i] === ':' || text[i] === '|') {
                i++;
                let depth = 0;
                while (i < text.length) {
                    if (chOpen(text[i])) depth++;
                    else if (chClose(text[i]) && depth > 0) depth--;
                    else if (depth === 0 && (text[i] === ',' || text.startsWith('=>', i))) break;
                    i++;
                }
            }
            if (text.startsWith('=>', i)) i += 2;
            else if (text.startsWith('↦', i)) i += 2;
            else if (text[i] === ',') i++;
            const inner = new Set(bound);
            for (const n of local) inner.add(n);
            for (const n of freeNames(text.slice(i), inner)) found.add(n);
            return found;
        }
        ID_RE.lastIndex = i;
        const m = ID_RE.exec(text);
        if (m && m.index === i) {
            if (!bound.has(m[0])) found.add(m[0]);
            i = ID_RE.lastIndex;
            continue;
        }
        i++;
    }
    return found;
}

const CLOSE_OF = { '(': ')', '{': '}', '[': ']', '⦃': '⦄' };
function chOpen(c) { return c === '(' || c === '{' || c === '[' || c === '⦃'; }
function chClose(c) { return c === ')' || c === '}' || c === ']' || c === '⦄'; }

function freeMentions(type, name) {
    return freeNames(type).has(name);
}

/** `⊆` / `⊂` / `⊇` / `⊃` / `∈` / `∉` — relations whose LHS may be a set literal. */
const SET_REL = /[⊆⊂⊇⊃∈∉]/;

/**
 * Find `({…} : Set _)` wrapping a brace set-literal on the LHS of a set relation.
 * Returns `{ start, ascription }` into `type`, or null.
 * Conservative: no nested `{` inside the literal; `Set` must be a bare token.
 */
function findRedundantSetAscription(type) {
    for (let i = 0; i < type.length; i++) {
        if (type[i] !== '(') continue;
        let j = i + 1;
        while (j < type.length && /\s/.test(type[j])) j++;
        if (type[j] !== '{') continue;
        const openBrace = j;
        const closeBrace = type.indexOf('}', openBrace + 1);
        if (closeBrace < 0) continue;
        if (type.slice(openBrace + 1, closeBrace).includes('{')) continue;
        j = closeBrace + 1;
        while (j < type.length && /\s/.test(type[j])) j++;
        if (type[j] !== ':') continue;
        j++;
        while (j < type.length && /\s/.test(type[j])) j++;
        if (!type.startsWith('Set', j)) continue;
        const after = type[j + 3] ?? '';
        if (/[\p{L}\p{N}_]/u.test(after)) continue; // e.g. Setoid
        let depth = 0;
        let k = i;
        for (; k < type.length; k++) {
            if (type[k] === '(') depth++;
            else if (type[k] === ')') {
                depth--;
                if (depth === 0) break;
            }
        }
        if (depth !== 0) continue;
        let r = k + 1;
        while (r < type.length && /\s/.test(type[r])) r++;
        if (!SET_REL.test(type[r] ?? '')) continue;
        return { start: i, ascription: type.slice(i, k + 1) };
    }
    return null;
}

/** Identifier uses of `name` on [from, end) of the comment-blanked source (same idea as binder-underscore-name). */
/** Identifier uses of `name` in the half-open source range [fromLine:fromCol, toLine:toCol). */
function countNameUsesRange(P, name, fromLine, fromCol, toLine, toCol) {
    if (!name || name === '_') return 0;
    if (toLine < fromLine || (toLine === fromLine && toCol <= fromCol)) return 0;
    let n = 0;
    for (let i = fromLine; i <= toLine; i++) {
        const l = P.code[i];
        if (l == null) break;
        const start = i === fromLine ? fromCol : 0;
        const stop = i === toLine ? Math.min(toCol, l.length) : l.length;
        if (start >= stop) continue;
        let k = start - 1;
        while ((k = l.indexOf(name, k + 1)) >= 0 && k < stop) {
            if (k + name.length > stop) break;
            const before = l[k - 1];
            const after = l[k + name.length];
            if ((before && /[\p{L}\p{N}_'.!?]/u.test(before)) || (after && /[\p{L}\p{N}_'!?₀-₉]/u.test(after))) continue;
            // binding sites (`name :`, intro / fun / pattern binders), not uses
            if (/^\s*:(?!=)/.test(l.slice(k + name.length))) continue;
            if (isBinderKeywordContext(l, k)) continue;
            n++;
        }
    }
    return n;
}

function countNameUses(P, name, from, end) {
    return countNameUsesRange(P, name, from, 0, end, 0);
}

/**
 * Tactics that consume a context hypothesis without naming it.
 * Not `simp` / `exact` / `refine` / `convert` / `simpa`: those often appear in proofs that
 * do not use a `_` given (see the Qkd `main` ∀-y example); implicit-argument uses may
 * therefore be false positives (documented in the README).
 */
function proofMayUseUnnamedHyp(P, from, end) {
    for (let i = from; i < end; i++) {
        const l = P.code[i];
        if (l.includes('‹')) return true;
        if (/(^|[^\p{L}\p{N}_'])(assumption|apply_assumption)(?![\p{L}\p{N}_'])/u.test(l)) return true;
    }
    return false;
}

function showGivenBinder(g) {
    const o = g.open || '(';
    const c = closeOf(o);
    const flat = String(g.flat || '').replace(/\s+/g, ' ');
    const body = flat.length > 80 ? `${flat.slice(0, 79)}…` : flat;
    return `${o}${body}${c}`;
}

/** Proposition `-- given` hypothesis (not an expression binder, not `{…}` / `[…]` above `-- given`). */
function isGivenHypothesis(g, propClasses) {
    if (g.kind !== 'explicit' || !g.names.length || g.deflt != null) return false;
    const t = String(g.type || '').trim();
    if (!t || t === 'Prop') return false;
    if (propKind(g) === 'prop') return true;
    return isPropositionType(t, propClasses);
}

/**
 * `-- given` hypothesis that never appears as a use in the proof: drop it, even when already `_`.
 * Named uses follow binder-underscore-name (identifier occurrences, skipping binding sites).
 * After `fun` / `λ` `=>` / `↦`, later identifiers on the line are uses (including `h₀.1` / `h₀.2`).
 * A name still needed in a later given / the imply is kept (often `given-implicit-dep`).
 * A `class … : Prop` hypothesis (`SinglePSpace`, …) is kept for instance search even when unnamed in the proof.
 */
function givenUnusedRule(ctx, d, sig, gg) {
    const { P } = ctx;
    const { given, imply, proof } = d.markers;
    if (given == null || !gg.length) return;
    const proofFrom = proof != null ? proof + 1
        : (sig.assign != null ? sig.assign.line + (String(P.code[sig.assign.line] || '').includes('by') ? 1 : 0) : null);
    if (proofFrom == null || proofFrom >= d.end) return;
    // later signature: other givens after this binder, plus `-- imply` up to the proof / `:=`
    const sigEnd = proof != null ? proof : (sig.assign != null ? sig.assign.line : d.end);
    let propClasses = null;
    const unnamedOk = proofMayUseUnnamedHyp(P, proofFrom, d.end);
    for (const g of gg) {
        if (propClasses == null) {
            propClasses = new Set(propClassNames(ctx.root));
            if (ctx.source && /\bclass\s/.test(ctx.source)) collectPropClasses(ctx.source, propClasses);
        }
        if (!isGivenHypothesis(g, propClasses)) continue;
        if (isPropClassType(g.type, propClasses)) continue;
        const unused = [];
        for (const name of g.names) {
            if (name !== '_') {
                if (countNameUses(P, name, proofFrom, d.end) > 0) continue;
                // still required by a later given or the imply
                const afterBinder = g.endLine != null ? g.endLine + 1 : g.line + 1;
                if (countNameUses(P, name, afterBinder, Math.min(sigEnd, proofFrom)) > 0) continue;
            } else if (unnamedOk) {
                continue;
            }
            unused.push(name);
        }
        if (!unused.length) continue;
        const shown = showGivenBinder(g);
        const all = unused.length === g.names.length;
        const msg = all
            ? `${shown} is unused in the proof: this \`-- given\` hypothesis is unnecessary and should be dropped`
            : `\`${unused.join('`, `')}\` in ${shown} is unused in the proof: this \`-- given\` hypothesis is unnecessary and should be dropped`;
        ctx.warn('given-unused', g.line + 1, g.col + 1, msg);
    }
}

/**
 * Named instance binder `[h : T]` above `-- given` that is never used in a later
 * signature binder, the `-- given` section, or the `-- imply` / conclusion should
 * be written anonymously as `[T]`. Mentions in the `-- proof` body do not count.
 * `[_ : T]` is the same unused named form and should also become `[T]`.
 * Already-anonymous `[T]` is left alone. Binders under `-- given` stay on
 * `inst-under-given` (named `[h : T]` becomes `(h : T)` there).
 */
function instUnusedRule(ctx, d, sig) {
    const { P } = ctx;
    const { given, imply, proof } = d.markers;
    const preEnd = given ?? imply ?? (sig.colon ? sig.colon.line + 1 : (sig.assign ? sig.assign.line : d.end));
    let toLine;
    let toCol;
    if (proof != null) {
        // given + imply only; the `-- proof` line and body are excluded
        toLine = proof;
        toCol = 0;
    } else if (sig.assign != null) {
        // conclusion up to `:=`; tactics after `:=` are the proof
        toLine = sig.assign.line;
        toCol = sig.assign.col;
    } else {
        toLine = d.end - 1;
        toCol = (P.code[d.end - 1] || '').length;
        if (toLine < d.line) return;
    }
    for (const g of sig.groups) {
        if (g.kind !== 'instImplicit' || !g.names.length || g.line >= preEnd) continue;
        const fromLine = g.endLine != null ? g.endLine : g.line;
        const fromCol = (g.endCol != null ? g.endCol : g.col) + 1;
        const unused = [];
        for (const name of g.names) {
            if (name !== '_' && countNameUsesRange(P, name, fromLine, fromCol, toLine, toCol) > 0) continue;
            unused.push(name);
        }
        if (!unused.length) continue;
        const shown = `[${g.flat}]`;
        const anon = `[${g.type}]`;
        const all = unused.length === g.names.length;
        const msg = all
            ? `${shown} is unused in \`-- given\` / \`-- imply\`: simplify to the anonymous instance binder \`${anon}\``
            : `\`${unused.join('`, `')}\` in ${shown} is unused in \`-- given\` / \`-- imply\`: simplify the unused name to the anonymous instance binder \`${anon}\``;
        ctx.warn('inst-unused', g.line + 1, g.col + 1, msg);
    }
}

/**
 * Semicolon-separated statements in `-- imply` should be newline-separated
 * by omitting `;`. Tactic-mode `;` in `-- proof` and separators in `-- given`
 * are out of scope. Comments / strings are already blanked by `prepare()`.
 */
const IMPLY_OPEN = { '(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄', '⁅': '⁆' };
const IMPLY_CLOSE = { ')': '(', ']': '[', '}': '{', '⟩': '⟨', '⦄': '⦃', '⁆': '⁅' };

/**
 * True when `assign` (`:=`) ends the `-- imply` region rather than belonging
 * to a `let` / `have` / similar binding whose right-hand side or a later imply
 * statement still follows. `:= by` / `:= calc` ends the region only when no
 * later line at the same indent remains before `stopLine`.
 */
function implyAssignEndsRegion(P, assign, stopLine) {
    const line = P.code[assign.line] ?? '';
    const stmtIndent = line.length - line.trimStart().length;
    const after = line.slice(assign.col + 2);
    const trimmed = after.trim();
    if (trimmed && !/^(by|calc)\b/.test(trimmed)) return false;
    for (let i = assign.line + 1; i < stopLine && i < P.code.length; i++) {
        const l = P.code[i] ?? '';
        if (!l.trim()) continue;
        const indent = l.length - l.trimStart().length;
        if (indent <= stmtIndent) return false;
    }
    return true;
}

/** First line/col that ends the `-- imply` region: the lemma `:=`, else `-- proof`. */
function implyRegionEnd(P, d, sig) {
    const { imply, proof } = d.markers;
    const stopLine = proof != null && proof > imply ? proof : d.end;
    const st = [];
    let lastAssign = null;
    const lastLine = Math.min(stopLine, P.code.length - 1);
    for (let i = imply + 1; i <= lastLine; i++) {
        if (proof != null && i === proof) break;
        const l = P.code[i] ?? '';
        for (let j = 0; j < l.length; j++) {
            const ch = l[j];
            if (IMPLY_CLOSE[ch] && st.length && st[st.length - 1] === IMPLY_CLOSE[ch]) st.pop();
            else if (IMPLY_OPEN[ch]) st.push(ch);
            if (st.length === 0 && ch === ':' && l[j + 1] === '=') {
                lastAssign = { line: i, col: j };
                j++;
            }
        }
    }
    if (lastAssign && implyAssignEndsRegion(P, lastAssign, stopLine)) return lastAssign;
    if (sig.assign && (sig.assign.line > imply || (sig.assign.line === imply && sig.assign.col > 0))
        && implyAssignEndsRegion(P, sig.assign, stopLine))
        return sig.assign;
    return { line: stopLine, col: 0 };
}

/** True when more non-space code follows `;` on the same line, still inside the imply span. */
function implySemicolonHasSameLineFollow(P, line, col, end) {
    const l = P.code[line] ?? '';
    const limit = line === end.line ? end.col : l.length;
    return /\S/.test(l.slice(col + 1, limit));
}

/**
 * After a `by` at depth 0, a `;` that still has a more-indented (or same-line)
 * continuation is a tactic separator, not an imply statement separator.
 */
function implySemicolonIsInteriorBy(P, line, col, stmtIndent, end) {
    if (implySemicolonHasSameLineFollow(P, line, col, end)) return true;
    const last = Math.min(end.line, P.code.length - 1);
    for (let i = line + 1; i <= last; i++) {
        const raw = P.code[i] ?? '';
        const slice = raw.slice(0, i === end.line ? end.col : raw.length);
        if (!slice.trim()) continue;
        const indent = slice.length - slice.trimStart().length;
        return indent > stmtIndent;
    }
    return false;
}

/**
 * Top-level `;` in `-- imply` (e.g. `let` / `have` terminated with `;` before
 * the conclusion, or several imply statements joined by `;`) should be omitted
 * in favor of a newline.
 */
function implySemicolonRule(ctx, d, sig) {
    const { P } = ctx;
    const { imply } = d.markers;
    if (imply == null) return;
    const end = implyRegionEnd(P, d, sig);
    const lastLine = Math.min(end.line, P.code.length - 1);
    if (imply + 1 > lastLine) return;
    const st = [];
    let stmtIndent = null;
    let inBy = false;
    for (let i = imply + 1; i <= lastLine; i++) {
        const l = P.code[i] ?? '';
        const limit = i === end.line ? end.col : l.length;
        const prefix = l.slice(0, limit);
        if (prefix.trim()) {
            const indent = prefix.length - prefix.trimStart().length;
            if (st.length === 0 && (stmtIndent == null || indent <= stmtIndent)) {
                stmtIndent = indent;
                inBy = false;
            }
        }
        for (let j = 0; j < limit; j++) {
            const ch = l[j];
            if (IMPLY_CLOSE[ch] && st.length && st[st.length - 1] === IMPLY_CLOSE[ch]) st.pop();
            else if (IMPLY_OPEN[ch]) st.push(ch);
            if (st.length !== 0) continue;
            if (ch === ';') {
                const interior = inBy && implySemicolonIsInteriorBy(P, i, j, stmtIndent ?? 0, end);
                if (!interior) {
                    const sameLine = implySemicolonHasSameLineFollow(P, i, j, end);
                    const msg = sameLine
                        ? 'semicolon-separated statements in `-- imply`: omit `;` and put the following statement on a new line'
                        : 'semicolon-separated statements in `-- imply`: omit `;` and keep the following statement on a new line';
                    ctx.warn('imply-semicolon', i + 1, j + 1, msg);
                    inBy = false;
                }
                continue;
            }
            if (l.startsWith('by', j) && !isIdentChar(l[j - 1]) && !isIdentChar(l[j + 2])) inBy = true;
        }
    }
}

/**
 * Named `let` / `have` binders in `-- imply` that are never used later in
 * `-- imply` or in the `-- proof` should drop the name (`let h : T :=` →
 * `let : T :=`, `have h :=` → `have :=`). Mentions in the proof *do* count:
 * dropping the name would break a proof that refers to it (unlike `inst-unused`,
 * where an anonymous instImplicit is still found by typeclass inference).
 * Already-anonymous `let : T :=` / `have : T :=` / `let :=` / `have :=` are
 * left alone. `let _ : T :=` / `have _ :=` are the same unused named form and
 * should also drop `_`. Pattern binders (`let ⟨a, b⟩ :=`), `let rec` / `let mut`,
 * and function lets (`let f x :=`, `let f (x : T) :=`) are left alone.
 * Only statement-level `-- imply` binders (not `-- given`, not `-- proof`,
 * not a `let` / `have` interior to a depth-0 `by` block).
 */
function implyPosBefore(line, col, end) {
    return line < end.line || (line === end.line && col < end.col);
}

function implySkipWs(P, line, col, end) {
    while (implyPosBefore(line, col, end)) {
        const l = P.code[line] ?? '';
        const limit = line === end.line ? Math.min(end.col, l.length) : l.length;
        while (col < limit && /\s/.test(l[col])) col++;
        if (col < limit) return { line, col };
        line++;
        col = 0;
    }
    return null;
}

function implyStartsWith(P, line, col, end, token) {
    const l = P.code[line] ?? '';
    const limit = line === end.line ? Math.min(end.col, l.length) : l.length;
    return col + token.length <= limit && l.startsWith(token, col);
}

function implySliceFlat(P, fromLine, fromCol, toLine, toCol) {
    let text;
    if (fromLine === toLine) text = (P.raw[fromLine] ?? '').slice(fromCol, toCol);
    else {
        const parts = [(P.raw[fromLine] ?? '').slice(fromCol)];
        for (let i = fromLine + 1; i < toLine; i++) parts.push(P.raw[i] ?? '');
        parts.push((P.raw[toLine] ?? '').slice(0, toCol));
        text = parts.join(' ');
    }
    return text.replace(/\s+/g, ' ').trim();
}

function implyTruncate(s, max = 80) {
    return s.length > max ? `${s.slice(0, max - 1)}…` : s;
}

const IMPLY_LET_HAVE_IDENT = /^[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*/u;
const IMPLY_LET_HAVE_SPECIAL = /^(rec|mut)(?![\p{L}\p{N}_'])/u;
const IMPLY_PATTERN_OPEN = new Set(['⟨', '(', '{', '[', '⦃']);

/** First depth-0 `:=` in the imply span starting at (line, col). */
function implyFindAssign(P, line, col, end) {
    const st = [];
    while (implyPosBefore(line, col, end)) {
        const l = P.code[line] ?? '';
        const limit = line === end.line ? Math.min(end.col, l.length) : l.length;
        if (col >= limit) {
            line++;
            col = 0;
            continue;
        }
        const ch = l[col];
        if (IMPLY_CLOSE[ch] && st.length && st[st.length - 1] === IMPLY_CLOSE[ch]) st.pop();
        else if (IMPLY_OPEN[ch]) st.push(ch);
        else if (st.length === 0 && ch === ':' && l[col + 1] === '=' && col + 1 < limit) return { line, col };
        col++;
    }
    return null;
}

/**
 * End of a `let` / `have` RHS starting just after `:=`, still inside the imply
 * span: a depth-0 `;` (returned after the semicolon), a later line at
 * `stmtIndent` or less, or `end` itself.
 */
function implyLetHaveRhsEnd(P, fromLine, fromCol, end, stmtIndent) {
    const st = [];
    let line = fromLine;
    let col = fromCol;
    let last = { line: fromLine, col: fromCol };
    while (implyPosBefore(line, col, end)) {
        const l = P.code[line] ?? '';
        const limit = line === end.line ? Math.min(end.col, l.length) : l.length;
        if (col >= limit) {
            let next = line + 1;
            while (true) {
                if (next > end.line) return { line: end.line, col: end.col };
                if (next === end.line && end.col === 0) return { line: end.line, col: end.col };
                if (!implyPosBefore(next, 0, end) && !(next === end.line && end.col > 0)) {
                    return { line: end.line, col: end.col };
                }
                const nl = P.code[next] ?? '';
                const nlimit = next === end.line ? Math.min(end.col, nl.length) : nl.length;
                const slice = nl.slice(0, nlimit);
                if (!slice.trim()) {
                    next++;
                    continue;
                }
                const indent = slice.length - slice.trimStart().length;
                if (st.length > 0 || indent > stmtIndent) {
                    line = next;
                    col = 0;
                    break;
                }
                return last;
            }
            continue;
        }
        const ch = l[col];
        if (IMPLY_CLOSE[ch] && st.length && st[st.length - 1] === IMPLY_CLOSE[ch]) st.pop();
        else if (IMPLY_OPEN[ch]) st.push(ch);
        else if (st.length === 0 && ch === ';') return { line, col: col + 1 };
        last = { line, col: col + 1 };
        col++;
    }
    return { line: end.line, col: end.col };
}

/**
 * Parse a statement-level `let` / `have` at (line, col) (the keyword start).
 * Returns the binder, or null when the form is skipped (already anonymous,
 * pattern, `let rec` / `let mut`, function let, or no `:=`).
 */
function parseImplyLetHave(P, line, col, end) {
    const l0 = P.code[line] ?? '';
    let kw = null;
    if (l0.startsWith('let', col) && !isIdentChar(l0[col + 3])) kw = 'let';
    else if (l0.startsWith('have', col) && !isIdentChar(l0[col + 4])) kw = 'have';
    if (!kw) return null;
    let pos = implySkipWs(P, line, col + kw.length, end);
    if (!pos) return null;
    const afterKw = (P.code[pos.line] ?? '').slice(pos.col);
    if (IMPLY_LET_HAVE_SPECIAL.test(afterKw)) return null;
    if (implyStartsWith(P, pos.line, pos.col, end, ':=')) return null;
    if (implyStartsWith(P, pos.line, pos.col, end, ':')) return null;
    const ch = (P.code[pos.line] ?? '')[pos.col];
    if (IMPLY_PATTERN_OPEN.has(ch)) return null;
    const ident = IMPLY_LET_HAVE_IDENT.exec(afterKw);
    if (!ident) return null;
    const name = ident[0];
    const nameLine = pos.line;
    const nameCol = pos.col;
    pos = implySkipWs(P, nameLine, nameCol + name.length, end);
    if (!pos) return null;
    if (implyStartsWith(P, pos.line, pos.col, end, ':=')) {
        return { kw, name, nameLine, nameCol, typed: false, type: '', assign: pos };
    }
    const nextCh = (P.code[pos.line] ?? '')[pos.col];
    if (nextCh === ':' && !implyStartsWith(P, pos.line, pos.col, end, ':=')) {
        const typeStart = { line: pos.line, col: pos.col + 1 };
        const assign = implyFindAssign(P, typeStart.line, typeStart.col, end);
        if (!assign) return null;
        const type = implySliceFlat(P, typeStart.line, typeStart.col, assign.line, assign.col);
        return { kw, name, nameLine, nameCol, typed: true, type, assign };
    }
    // function let (`let f x :=`, `let f (x : T) :=`) or other special form
    return null;
}

function implyUnusedRule(ctx, d, sig) {
    const { P } = ctx;
    const { imply } = d.markers;
    if (imply == null) return;
    const end = implyRegionEnd(P, d, sig);
    const lastLine = Math.min(end.line, P.code.length - 1);
    if (imply + 1 > lastLine) return;
    const useToLine = d.end - 1;
    const useToCol = (P.code[useToLine] || '').length;
    const st = [];
    let stmtIndent = null;
    let inBy = false;
    for (let i = imply + 1; i <= lastLine; i++) {
        const l = P.code[i] ?? '';
        const limit = i === end.line ? end.col : l.length;
        const prefix = l.slice(0, limit);
        if (prefix.trim()) {
            const indent = prefix.length - prefix.trimStart().length;
            if (st.length === 0 && (stmtIndent == null || indent <= stmtIndent)) {
                stmtIndent = indent;
                inBy = false;
            }
        }
        for (let j = 0; j < limit; j++) {
            const ch = l[j];
            if (IMPLY_CLOSE[ch] && st.length && st[st.length - 1] === IMPLY_CLOSE[ch]) st.pop();
            else if (IMPLY_OPEN[ch]) st.push(ch);
            if (st.length !== 0) continue;
            if (l.startsWith('by', j) && !isIdentChar(l[j - 1]) && !isIdentChar(l[j + 2])) inBy = true;
            if (inBy) continue;
            const isLet = l.startsWith('let', j) && !isIdentChar(l[j - 1]) && !isIdentChar(l[j + 3]);
            const isHave = l.startsWith('have', j) && !isIdentChar(l[j - 1]) && !isIdentChar(l[j + 4]);
            if (!isLet && !isHave) continue;
            const binder = parseImplyLetHave(P, i, j, end);
            if (!binder) continue;
            const rhsEnd = implyLetHaveRhsEnd(P, binder.assign.line, binder.assign.col + 2, end, stmtIndent ?? 0);
            if (binder.name !== '_' && countNameUsesRange(P, binder.name, rhsEnd.line, rhsEnd.col, useToLine, useToCol) > 0) continue;
            const shownType = binder.typed ? implyTruncate(binder.type) : '';
            const shown = binder.typed
                ? `${binder.kw} ${binder.name} : ${shownType} :=`
                : `${binder.kw} ${binder.name} :=`;
            const anon = binder.typed
                ? `${binder.kw} : ${shownType} :=`
                : `${binder.kw} :=`;
            ctx.warn(
                'imply-unused',
                binder.nameLine + 1,
                binder.nameCol + 1,
                `\`${shown}\` is unused in the rest of \`-- imply\` and the \`-- proof\`: drop the name and write \`${anon}\``,
            );
        }
    }
}

export function signatureRules(ctx) {
    const { P, decls } = ctx;
    for (const d of decls) {
        if (!isLemma(d)) continue;
        const sig = parseSignature(P, d);
        d.sig = sig;
        const { given, imply, proof } = d.markers;
        const groups = sig.groups;
        const where = d.name && d.name !== 'main' ? ` of \`${d.name}\`` : '';
        const needsGiven = explicitGivenBinders(groups).length > 0;

        // ---- section markers (`-- given` / `-- imply` / `-- proof`) ------------------------------------------
        if (needsSectionMarkers(d, ctx)) {
            if (given == null) {
                // omit `-- given` when nothing belongs under it (type binders stay above)
                if (needsGiven) {
                    ctx.warn(
                        'section-given',
                        d.line + 1,
                        1,
                        `no \`-- given\` marker${where}: put hypotheses and explicit expression binders under \`-- given\``,
                    );
                }
            } else if (imply != null && given > imply) {
                ctx.warn('section-given', given + 1, 1, `\`-- given\` marker after \`-- imply\`${where}; order is given, imply, proof`);
            } else if (proof != null && given > proof) {
                ctx.warn('section-given', given + 1, 1, `\`-- given\` marker after \`-- proof\`${where}; order is given, imply, proof`);
            }
            if (given != null && givenRegionBlank(P, given, givenRegionEnd(d, sig))) {
                ctx.warn(
                    'section-given-empty',
                    given + 1,
                    1,
                    `no content under \`-- given\`${where}; delete the \`-- given\` marker`,
                );
            }
            if (imply == null) {
                ctx.warn('section-imply', d.line + 1, 1, `no \`-- imply\` marker${where}: put the conclusion after \`-- imply\``);
            } else if (sig.colon && sig.colon.line <= imply) {
                // conclusion text must start after the marker
                const end = sig.assign ?? { line: d.end, col: 0 };
                let text = '';
                for (let i = sig.colon.line; i < imply && i <= end.line; i++) {
                    const l = P.code[i];
                    const a = i === sig.colon.line ? sig.colon.col + 1 : 0;
                    const b = i === end.line ? end.col : l.length;
                    text += l.slice(a, b);
                }
                if (text.trim()) ctx.warn('section-imply', sig.colon.line + 1, sig.colon.col + 1, `the conclusion${where} starts before \`-- imply\`; move it below the marker`);
            } else if (proof != null && imply > proof) {
                ctx.warn('section-imply', imply + 1, 1, `\`-- imply\` marker after \`-- proof\`${where}; order is given, imply, proof`);
            }
            if (sig.assign) {
                // `-- proof` is mandatory for every proof shape. A bare `:= by` used to be the only
                // missing-marker hit; `:= calc`, `:= by rw …`, and a term after `:=` skipped it.
                if (proof == null) {
                    ctx.warn('section-proof', sig.assign.line + 1, sig.assign.col + 1, `no \`-- proof\` marker${where}: put the proof body after \`-- proof\``);
                } else if (proof < sig.assign.line) {
                    ctx.warn('section-proof', proof + 1, 1, `\`-- proof\` marker above the \`:=\`${where}`);
                } else {
                    for (let i = sig.assign.line + 1; i < proof; i++) {
                        if (P.code[i].trim()) {
                            ctx.warn('section-proof', i + 1, P.indent[i] + 1, `proof code${where} before the \`-- proof\` marker`);
                            break;
                        }
                    }
                }
            } else if (proof == null) {
                // no `:=` found: still require the marker on path/main lemmas
                ctx.warn('section-proof', d.line + 1, 1, `no \`-- proof\` marker${where}: put the proof body after \`-- proof\``);
            }
        }

        // ---- assign-by-proof: bare `:=` / `-- proof` / bare `by` -> `:= by` / `-- proof` ----------------------
        // Lemma files only. Scans forward from the assign (not limited to `d.end`): a column-0 `by` ends the
        // decl in findDecls before `-- proof` is recorded, so markers alone miss the anti-pattern.
        // Term-mode (`:=` / `-- proof` / term) stays quiet.
        if (ctx.isLemmaFile && sig.assign) {
            const rest = P.code[sig.assign.line].slice(sig.assign.col + 2).trim();
            if (!rest) {
                let i = sig.assign.line + 1;
                while (i < P.raw.length && /^\s*$/.test(P.raw[i])) i++;
                if (i < P.raw.length && /^\s*--\s*proof\s*$/.test(P.raw[i])) {
                    i++;
                    while (i < P.raw.length && /^\s*$/.test(P.raw[i])) i++;
                    if (i < P.code.length && /^by\s*$/.test(P.code[i].trim())) {
                        ctx.warn(
                            'assign-by-proof',
                            sig.assign.line + 1,
                            sig.assign.col + 1,
                            `bare \`:=\`${where} then \`-- proof\` then \`by\`: write \`:= by\` then \`-- proof\` (keep \`by\` on the \`:=\` line)`,
                        );
                    }
                }
            }
        }

        // ---- binders before `-- given` ----------------------------------------------------------------------
        const preEnd = given ?? imply ?? (sig.colon ? sig.colon.line + 1 : d.end);

        // ---- NeZero + basic scalar: prefer [NeZero (n : ℕ)] over {n : ℕ} [NeZero n] ------------------------
        // Standing Body rule via Real. Only the split style; fused `[NeZero (n : T)]` stays quiet.
        // ASCII Nat/Int/Rat/Real/Complex match the same five types (suggestion uses Unicode).
        const BASIC_NEZERO = new Map([
            ['ℕ', 'ℕ'], ['Nat', 'ℕ'],
            ['ℤ', 'ℤ'], ['Int', 'ℤ'],
            ['ℚ', 'ℚ'], ['Rat', 'ℚ'],
            ['ℝ', 'ℝ'], ['Real', 'ℝ'],
            ['ℂ', 'ℂ'], ['Complex', 'ℂ'],
        ]);
        const neZeroOf = (t) => {
            const m = /^NeZero\s+([\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*)$/u.exec(String(t || '').trim());
            return m ? m[1] : null;
        };
        /** instance line:col keys that already got `binder-nezero-fuse` (suppress conflicting `binder-dep-inst`) */
        const neZeroFusedInst = new Set();
        if (given != null || imply != null) {
            const basicImplicits = [];
            for (const g of groups) {
                if (g.line >= preEnd) continue;
                if (g.kind !== 'implicit' && g.kind !== 'strictImplicit') continue;
                const canon = BASIC_NEZERO.get(String(g.type || '').trim());
                if (!canon || !g.names.length) continue;
                for (const n of g.names) basicImplicits.push({ g, n, canon, written: String(g.type || '').trim() });
            }
            for (const g of groups) {
                if (g.line >= preEnd || g.kind !== 'instImplicit') continue;
                const tgt = neZeroOf(g.type);
                if (!tgt) continue;
                const hit = basicImplicits.find((x) => x.n === tgt);
                if (!hit) continue;
                const splitImp = hit.g.names.length === 1
                    ? `\`{${hit.n} : ${hit.written}}\``
                    : `\`{${hit.g.names.join(' ')} : ${hit.written}}\` (for \`${hit.n}\`)`;
                ctx.warn(
                    'binder-nezero-fuse',
                    hit.g.line + 1,
                    hit.g.col + 1,
                    `${splitImp} with \`[${g.flat}]\`: prefer \`[NeZero (${hit.n} : ${hit.canon})]\` over a split implicit + NeZero instance`,
                );
                neZeroFusedInst.add(`${g.line}:${g.col}`);
            }
        }

        const byLine = new Map();
        for (const g of groups) {
            if (g.line >= preEnd || (given == null && imply == null)) continue; // without markers: no "before given" region
            if (!byLine.has(g.line)) byLine.set(g.line, []);
            byLine.get(g.line).push(g);
        }
        const AUTO = /^(Type|Sort)\s*(\*|_)$/;
        const implicitNames = new Map(); // name -> line (auto-bound candidates excluded: they are to be omitted)
        const boundBy = new Map(); // line -> names bound on it
        for (const [line, gs] of byLine) {
            boundBy.set(line, gs.flatMap((g) => g.names));
            for (const g of gs) if ((g.kind === 'implicit' || g.kind === 'strictImplicit') && !AUTO.test(g.type)) for (const n of g.names) implicitNames.set(n, line);
        }
        const lineText = (gs) => gs.map((g) => g.flat).join(' ');
        const RANK = { standalone: 0, dependent: 1, bare: 2 };
        const LABEL = ['standalone instances', 'implicit binders with their dependent instances', 'bare implicit binders'];
        let maxRank = -1;
        let maxLine = -1;
        const rankOf = new Map();
        for (const [line, gs] of byLine) {
            const kinds = gs.map((g) => g.kind);
            if (kinds.includes('explicit') || kinds.includes('other')) continue;
            const imp = (k) => k === 'implicit' || k === 'strictImplicit';
            let cls;
            if (kinds.every((k) => k === 'instImplicit')) cls = 'standalone';
            else if (kinds.every(imp)) cls = 'bare';
            else {
                const firstInst = kinds.indexOf('instImplicit');
                const lastImp = kinds.map(imp).lastIndexOf(true);
                if (firstInst > 0 && lastImp < firstInst) cls = 'dependent';
                else {
                    ctx.warn('binder-order', line + 1, gs[0].col + 1, 'instance binder before an implicit binder on the same line: put the implicit binder first, then its dependent instances');
                    continue;
                }
            }
            const r = RANK[cls];
            // a standalone instance depending on an implicit is reported by `binder-dep-inst` instead
            const depOn = cls === 'standalone' ? [...implicitNames.keys()].find((n) => hasWord(lineText(gs), n)) : null;
            // the line could only move above lines it does not depend on
            const firstHigher = [...byLine.keys()].find((ln) => ln < line && rankOf.get(ln) > r);
            const uses = gs.map((g) => (g.names.length ? g.type : g.flat)).join(' ');
            const movable = firstHigher == null || ![...boundBy].some(([ln, names]) => ln >= firstHigher && ln < line && names.some((n) => hasWord(uses, n)));
            rankOf.set(line, r);
            if (r < maxRank && !depOn && movable) {
                ctx.warn('binder-order', line + 1, gs[0].col + 1, `line of ${LABEL[r]} after a line of ${LABEL[maxRank]} (line ${maxLine + 1}); order: standalone instances, implicit+dependent instances, bare implicits`);
            } else if (r > maxRank) { maxRank = r; maxLine = line; }

            // an instance on a standalone line that depends on an implicit declared on another pre-given line
            if (cls === 'standalone') {
                for (const g of gs) {
                    const dep = [...implicitNames.keys()].find((n) => hasWord(g.flat, n));
                    if (dep) {
                        // NeZero on ℕ/ℤ/ℚ/ℝ/ℂ prefers fusion, not same-line `{n : T} [NeZero n]`
                        if (neZeroFusedInst.has(`${g.line}:${g.col}`)) continue;
                        ctx.warn('binder-dep-inst', line + 1, g.col + 1, `instance \`[${g.flat}]\` depends on the implicit \`${dep}\` (line ${implicitNames.get(dep) + 1}); put it on that line, after the implicit binder`);
                        break;
                    }
                }
            }
        }

        // ---- binder-grouping: on a shared `{…}` + `[…]` line, every instance must constrain that line ----
        // Related = the instance's text mentions (a) a variable bound on that line — by the implicit `{p q : …}`
        // (mentioning just one of several names counts) or by an explicit `(p : ℕ)` next to it, so `[Fact p.Prime]`
        // belongs to the explicit `p`, not to `{R}` — or (b) an identifier occurring in the implicit's own type:
        // `{σ : ι → …} [Fintype ι]` groups fine because `ι` is part of `σ`'s type. Only an instance unrelated to
        // all of these is flagged: it belongs on its own line above the implicit binders (rank 0 for
        // `binder-order`, so hoisting never trips the order rule).
        for (const [line, gs] of byLine) {
            const imp = gs.filter((g) => g.kind === 'implicit' || g.kind === 'strictImplicit');
            if (!imp.length) continue;
            const insts = gs.filter((g) => g.kind === 'instImplicit');
            if (!insts.length) continue;
            const names = gs.filter((g) => g.kind !== 'instImplicit').flatMap((g) => g.names);
            const related = new Set(names);
            for (const g of imp) {
                for (const m of String(g.type || '').matchAll(/[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*/gu)) {
                    if (m[0] !== 'Type' && m[0] !== 'Sort' && m[0] !== 'Prop') related.add(m[0]);
                }
            }
            if (!related.size) continue;
            for (const g of insts) {
                if ([...related].some((n) => hasWord(g.flat, n))) continue;
                ctx.warn('binder-grouping', line + 1, g.col + 1,
                    `instance \`[${g.flat}]\` does not constrain any binder on this line (${names.map((n) => `\`${n}\``).join(', ')}); hoist it to its own line before the implicit binders`);
            }
        }

        // ---- auto-bound implicits: `{α : Type*}` / `{α : Sort*}` / `{α : Type _}` (conservative) ------------------
        for (const [line, gs] of byLine) {
            for (const g of gs) {
                if (g.kind !== 'implicit' || g.deflt != null || !/^(Type|Sort)\s*(\*|_)$/.test(g.type)) continue;
                ctx.warn('binder-auto-bound', line + 1, g.col + 1, `\`{${g.flat}}\` is auto-bound (autoImplicit): omit it`);
            }
        }

        // ---- default arguments must be in the given section ----------------------------------------------------
        for (const g of groups) {
            if (g.deflt == null) continue;
            const inGiven = given != null && g.line > given && (imply == null || g.line < imply);
            if (!inGiven) ctx.warn('default-arg-given', g.line + 1, g.col + 1, `default argument \`${g.open}${g.flat}${closeOf(g.open)}\` must be inside the \`-- given\` section`);
        }

        // ---- explicit (non-instance) binders belong under `-- given` ------------------------------------------
        // `{…}` / `⦃…⦄` / instance binders `[…]` (named or unnamed) stay in the pre-given region.
        // Lean defaults `(h : T := …)` are `default-arg-given`.
        if (given != null) {
            for (const g of groups) {
                if (g.kind !== 'explicit' || g.deflt != null || g.line >= given) continue;
                ctx.warn(
                    'explicit-above-given',
                    g.line + 1,
                    g.col + 1,
                    `explicit binder \`(${g.flat})\` is above \`-- given\`; move it under \`-- given\``,
                );
            }
        }

        // ---- given: named `[h : T]` becomes `(h : T)` here; unnamed `[T]` may move above. Never `(h : T := by tactic)` ----------
        const gg = given != null
            ? groups.filter((g) => g.line > given && (imply == null || g.line < imply))
            : [];
        for (const g of gg) {
            if (g.kind !== 'instImplicit') continue;
            const shown = `[${g.flat}]`;
            if (g.names.length) {
                ctx.warn(
                    'inst-under-given',
                    g.line + 1,
                    g.col + 1,
                    `${shown} under \`-- given\` should be changed to \`(${g.flat})\``,
                );
            } else {
                ctx.warn(
                    'inst-under-given',
                    g.line + 1,
                    g.col + 1,
                    `${shown} under \`-- given\` should be changed to \`(h : ${g.type})\`, or moved above \`-- given\``,
                );
            }
        }
        for (const g of gg) {
            // tactic-valued binder defaults are forbidden (incl. `:= by infer_instance`)
            if (g.deflt == null || !/^by\b/.test(g.deflt)) continue;
            ctx.warn(
                'given-inst',
                g.line + 1,
                g.col + 1,
                `binder default \`${g.open}${g.flat}${closeOf(g.open)}\` uses a tactic; never \`(h : T := by tactic)\` or \`(h : T := by infer_instance)\``,
            );
        }

        // ---- a proposition type must not take a term default `(h : P := e)` --------------------------------
        // `SinglePSpace` is `class … : Prop`. `(hSP : SinglePSpace π (x, s) := e)` is that default.
        // Tactic defaults stay on `given-inst`.
        {
            let propClasses = null;
            for (const g of groups) {
                if (g.kind !== 'explicit' || g.deflt == null || /^by\b/.test(g.deflt)) continue;
                if (propClasses == null) {
                    propClasses = propClassNames(ctx.root);
                    if (ctx.source && /\bclass\s/.test(ctx.source)) collectPropClasses(ctx.source, propClasses = new Set(propClasses));
                }
                if (!isPropositionType(g.type, propClasses)) continue;
                ctx.warn(
                    'prop-default-arg',
                    g.line + 1,
                    g.col + 1,
                    `proposition type is taking default argument using \`:=\`: \`${g.open}${g.flat}${closeOf(g.open)}\``,
                );
            }
        }

        // ---- given: an explicit binder that a later binder (of any kind) mentions is an implicit above `-- given` ----
        // Text fallback of the AST rule (`mentions`). Whole-word `freeMentions`; a name rebound by ∀/∃/∑/∏/fun/λ
        // in the later binder's type does not count. A non-propositional dependent binder uses the "determined by"
        // wording (showing the whole binder); a later proposition keeps "referenced by".
        if (given != null && !ctx.astCovered.has('given-implicit-dep')) {
            for (const g of gg) {
                if (g.kind !== 'explicit' || g.deflt != null || !g.names.length || propKind(g) === 'prop') continue;
                if (propKind(g) == null && g.names.every((n) => /^_?h/.test(n))) continue;
                const hits = g.names.map((n) => {
                    const hyps = gg.filter((p) => p.line > g.line && p.type && freeMentions(p.type, n));
                    const prop = hyps.filter((p) => propKind(p) === 'prop');
                    const dep = hyps.filter((p) => propKind(p) !== 'prop');
                    return { n, hyps, prop, dep };
                });
                const referenced = hits.filter((h) => h.hyps.length);
                if (!referenced.length) continue;
                const shown = `(${g.flat})`;
                const hasDep = referenced.some((h) => h.dep.length);
                const desc = (h) => {
                    const parts = [];
                    if (h.dep.length) parts.push(`determined by ${h.dep.map((p) => `\`(${p.flat})\``).join(', ')}`);
                    const propNames = [...new Set(h.prop.flatMap((p) => p.names))];
                    if (propNames.length) parts.push(`referenced by ${propNames.map((n) => `\`${n}\``).join(', ')}`);
                    return parts.join(' and ');
                };
                if (referenced.length === g.names.length) {
                    const subject = hasDep ? referenced.map((h) => `\`${h.n}\``).join(', ') : `\`${shown}\``;
                    ctx.warn('given-implicit-dep', g.line + 1, g.col + 1,
                        `${subject} is ${referenced.map(desc).join('; ')}; it is not a given — change it to \`{${g.flat}}\` above \`-- given\``);
                } else {
                    for (const h of referenced) {
                        const subject = hasDep ? `\`${h.n}\`` : `\`${h.n}\` in \`${shown}\``;
                        ctx.warn('given-implicit-dep', g.line + 1, g.col + 1,
                            `${subject} is ${desc(h)}; it is not a given — change \`${h.n}\` to \`{${h.n} : …}\` above \`-- given\``);
                    }
                }
            }
        }

        // ---- given: propositions first, expressions next; propositions consecutive --------------------------------
        if (given != null && !ctx.astCovered.has('given-prop-first')) {
            // expressions the propositions need (closed over expression types): they must stay above the propositions
            const need = new Set();
            let grow = gg.filter((g) => propKind(g) === 'prop').map((g) => g.type);
            while (grow.length) {
                const next = [];
                for (const t of grow) for (const g of gg) {
                    if (propKind(g) !== 'expr' || g.names.every((n) => need.has(n)) || !g.names.some((n) => hasWord(t, n))) continue;
                    for (const n of g.names) need.add(n);
                    next.push(g.type);
                }
                grow = next;
            }
            let warned = false;
            for (let a = 0; a < gg.length; a++) {
                if (propKind(gg[a]) !== 'expr' || gg[a].names.some((n) => need.has(n))) continue;
                const names = gg[a].names;
                const later = gg.slice(a + 1);
                // the proposition must not mention the expression (dependency forces the order)
                const prop = later.find((g) => propKind(g) === 'prop' && !names.some((n) => hasWord(g.flat, n)));
                if (!prop) continue;
                // nothing between them may depend on the expression either
                const between = gg.slice(a + 1, gg.indexOf(prop));
                if (between.some((g) => names.some((n) => hasWord(g.flat, n)))) continue;
                ctx.warn('given-prop-first', prop.line + 1, prop.col + 1, `proposition \`(${prop.flat})\` after the expression \`(${gg[a].flat})\` (line ${gg[a].line + 1}): in \`given\`, propositions come first`);
                warned = true;
                break;
            }
            // `given-prop-consecutive` (text fallback of the AST rule): prop … expr … prop
            if (!warned) {
                const typed = gg.filter((g) => g.deflt == null && propKind(g) != null);
                const p0 = typed.findIndex((g) => propKind(g) === 'prop');
                const g0 = p0 < 0 ? -1 : typed.findIndex((g, i) => i > p0 && propKind(g) === 'expr');
                const late = g0 < 0 ? -1 : typed.findIndex((g, i) => i > g0 && propKind(g) === 'prop');
                if (late >= 0) {
                    const prop = typed[late];
                    const gap = typed.slice(g0, late).filter((g) => propKind(g) === 'expr');
                    const exprs = typed.filter((g) => propKind(g) === 'expr');
                    const before = exprs.filter((g) => g.names.some((n) => need.has(n)));
                    const after = exprs.filter((g) => !g.names.some((n) => need.has(n)));
                    const props = typed.filter((g) => propKind(g) === 'prop');
                    const nm = (xs) => xs.flatMap((g) => g.names).join(' ');
                    const fix = gap.some((g) => g.names.some((n) => need.has(n)))
                        ? `move ${before.filter((g) => typed.indexOf(g) > p0).map((g) => `\`(${g.flat})\``).join(' ')} before \`(${typed[p0].flat})\` (order: ${[before, props, after].filter((xs) => xs.length).map((xs) => `\`${nm(xs)}\``).join(', then ')})`
                        : 'move it up to the propositions above';
                    ctx.warn('given-prop-consecutive', prop.line + 1, prop.col + 1,
                        `proposition \`(${prop.flat})\` is separated from the propositions above by ${gap.map((g) => `\`(${g.flat})\``).join(' ')}: in \`given\`, keep all propositions consecutive (only the first run is typeset); ${fix}`);
                }
            }
        }

        // ---- given: numbered hyps h₀… / h0… start at 0, no gaps, lower index earlier (descriptive hG/hr OK) ----
        if (given != null && gg.length) {
            const numbered = [];
            let preferSub = false;
            for (const g of gg) {
                if (g.kind !== 'explicit') continue;
                for (const n of g.names) {
                    const idx = numberedHypIndex(n);
                    if (idx == null) continue;
                    if (/^h[₀₁₂₃₄₅₆₇₈₉]$/.test(n)) preferSub = true;
                    numbered.push({ idx, name: n, line: g.line, col: g.col });
                }
            }
            if (numbered.length) {
                const allIdxs = [...new Set(numbered.map((h) => h.idx))].sort((a, b) => a - b);
                const have = allIdxs.map((i) => hypLabel(i, preferSub)).join(', ');
                const seen = new Set();
                let warned = false;
                for (const h of numbered) {
                    if (!warned) {
                        const missingBefore = [];
                        for (let i = 0; i < h.idx; i++) if (!seen.has(i)) missingBefore.push(i);
                        if (missingBefore.length) {
                            // source order: h₁ before any h₀, or h₂ without prior h₀/h₁, etc.
                            if (!seen.has(0)) {
                                ctx.warn('given-hyp-index', h.line + 1, h.col + 1,
                                    `\`${h.name}\` appears without a prior \`${hypLabel(0, preferSub)}\` (have ${have}; put \`${hypLabel(0, preferSub)}\` first among numbered given hyps)`);
                            } else {
                                const miss = missingBefore.map((i) => hypLabel(i, preferSub)).join(', ');
                                ctx.warn('given-hyp-index', h.line + 1, h.col + 1,
                                    `gap in numbered given hyps: \`${h.name}\` appears without prior ${miss} (have ${have} but missing ${miss})`);
                            }
                            warned = true;
                        }
                    }
                    seen.add(h.idx);
                }
            }
        }


        // ---- given: drop redundant `({…} : Set _)` on the LHS of ⊆/⊂/∈/… ---------------------------------
        if (given != null && gg.length) {
            for (const g of gg) {
                if (g.kind !== 'explicit' || !g.type) continue;
                const hit = findRedundantSetAscription(g.type);
                if (!hit) continue;
                let col = g.col + 1;
                const lineText = P.code[g.line] ?? '';
                const at = lineText.indexOf('({');
                if (at >= 0) col = at + 1;
                const lit = (hit.ascription.match(/\{[^{}]*\}/) || ['{…}'])[0];
                ctx.warn(
                    'redundant-set-ascription',
                    g.line + 1,
                    col,
                    `redundant \`${hit.ascription}\` on the LHS of a set relation: drop the \`: Set _\` ascription and write \`${lit}\``,
                );
            }
        }

        // ---- given: unused hypothesis (incl. already `_`) should be dropped --------------------------
        if (given != null) givenUnusedRule(ctx, d, sig, gg);

        // ---- unused named instImplicit `[h : T]` above `-- given` should be `[T]` --------------------
        instUnusedRule(ctx, d, sig);

        // ---- semicolon-separated `-- imply` statements should be newline-separated ------------------
        implySemicolonRule(ctx, d, sig);

        // ---- unused named `let` / `have` in `-- imply` should drop the name --------------------------
        implyUnusedRule(ctx, d, sig);

        // ---- combine adjacent binders of the same kind and type ------------------------------------------------
        for (let a = 0; a + 1 < groups.length; a++) {
            const g = groups[a];
            const h = groups[a + 1];
            if (g.kind === 'instImplicit' || g.kind !== h.kind || !g.names.length || !h.names.length) continue;
            if (g.deflt != null || h.deflt != null || g.type !== h.type) continue;
            if (h.names.some((n) => hasWord(g.type, n)) || g.names.some((n) => hasWord(h.type, n))) continue;
            // only within one section
            const sec = (x) => (given != null && x.line > given ? 1 : 0) + (imply != null && x.line > imply ? 1 : 0);
            if (sec(g) !== sec(h)) continue;
            const o = g.open;
            const c = closeOf(o);
            ctx.warn('binder-combine', h.line + 1, h.col + 1, `combine \`${o}${g.flat}${c}\` and \`${o}${h.flat}${c}\` into \`${o}${[...g.names, ...h.names].join(' ')} : ${g.type}${c}\``);
        }
    }
}

function closeOf(o) {
    return { '(': ')', '{': '}', '[': ']', '⦃': '⦄' }[o] ?? '';
}
