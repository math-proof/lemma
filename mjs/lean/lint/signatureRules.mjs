/**
 * Signature rules of a lemma / theorem: binder lines before `-- given`, default arguments, combining binders,
 * `-- given` / `-- imply` / `-- proof` sections.
 */
import { parseSignature, hasWord } from './scan.mjs';

const REL = /[=≠<>≤≥∈∉⊆⊂⊇⊃∣↔∧∨¬≈≡]|∀|∃|\bTrue\b|\bFalse\b/;
const isLemma = (d) => d.kind === 'lemma' || d.kind === 'theorem';
const isMain = (d) => /^@\[\s*main\b/.test(d.attrs);

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

export function signatureRules(ctx) {
    const { P, decls } = ctx;
    for (const d of decls) {
        if (!isLemma(d)) continue;
        const sig = parseSignature(P, d);
        d.sig = sig;
        const { given, imply, proof } = d.markers;
        const groups = sig.groups;
        const main = isMain(d);
        const where = d.name && d.name !== 'main' ? ` of \`${d.name}\`` : '';

        // ---- section markers --------------------------------------------------------------------------------
        const hasMarkers = given != null || imply != null || proof != null;
        if (main || hasMarkers) {
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
            }
            if (sig.assign) {
                const rest = P.code[sig.assign.line].slice(sig.assign.col + 2).trim();
                const tactic = /^by\s*$/.test(rest);
                if (proof == null) {
                    if (tactic) ctx.warn('section-proof', sig.assign.line + 1, sig.assign.col + 1, `no \`-- proof\` marker${where}: put the proof body after \`-- proof\``);
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
            }
        }

        // ---- binders before `-- given` ----------------------------------------------------------------------
        const preEnd = given ?? imply ?? (sig.colon ? sig.colon.line + 1 : d.end);
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
                        ctx.warn('binder-dep-inst', line + 1, g.col + 1, `instance \`[${g.flat}]\` depends on the implicit \`${dep}\` (line ${implicitNames.get(dep) + 1}); put it on that line, after the implicit binder`);
                        break;
                    }
                }
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

        // ---- given: never `(h : T := by tactic)`; keep needed instances as `[…]` before the hyp ----------
        const gg = given != null
            ? groups.filter((g) => g.line > given && (imply == null || g.line < imply))
            : [];
        for (const g of gg) {
            // tactic-valued binder defaults are forbidden (incl. `:= by infer_instance`)
            if (g.deflt == null || !/^by\b/.test(g.deflt)) continue;
            const inst = g.names.length ? `[${g.names[0]} : ${g.type}]` : `[${g.type}]`;
            ctx.warn(
                'given-inst',
                g.line + 1,
                g.col + 1,
                `binder default \`${g.open}${g.flat}${closeOf(g.open)}\` uses a tactic; keep an instance binder \`${inst}\` inside \`-- given\`, before the hypothesis that needs it`,
            );
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
