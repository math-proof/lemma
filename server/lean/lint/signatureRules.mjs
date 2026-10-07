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

        // ---- given: propositions first, expressions next --------------------------------------------------------
        if (given != null && !ctx.astCovered.has('given-prop-first')) {
            const gg = groups.filter((g) => g.line > given && (imply == null || g.line < imply));
            for (let a = 0; a < gg.length; a++) {
                if (propKind(gg[a]) !== 'expr') continue;
                const names = gg[a].names;
                const later = gg.slice(a + 1);
                // the proposition must not mention the expression (dependency forces the order)
                const prop = later.find((g) => propKind(g) === 'prop' && !names.some((n) => hasWord(g.flat, n)));
                if (!prop) continue;
                // nothing between them may depend on the expression either
                const between = gg.slice(a + 1, gg.indexOf(prop));
                if (between.some((g) => names.some((n) => hasWord(g.flat, n)))) continue;
                ctx.warn('given-prop-first', prop.line + 1, prop.col + 1, `proposition \`(${prop.flat})\` after the expression \`(${gg[a].flat})\` (line ${gg[a].line + 1}): in \`given\`, propositions come first`);
                break;
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
