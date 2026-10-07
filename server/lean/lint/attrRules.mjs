/**
 * `attr-mp`: `X.is.Y.mp` / `.mpr` where `X.is.Y` is tagged `@[mp]` / `@[mpr]` → use the generated `Y.of.X` / `X.of.Y`.
 * `attr-comm`: `X.eq.Y.symm` or `← X.eq.Y` where `X.eq.Y` is tagged `@[comm]` → use the generated `Y.eq.X`.
 * The cited lemma is resolved through the file's `import Lemma.S.…` lines (and the opened sections), and its attributes
 * are read from `Lemma/S/….lean` under `ctx.root`; nothing is reported when the file cannot be resolved.
 */
import fs from 'node:fs';
import path from 'node:path';

const cache = new Map(); // abs path -> { mtimeMs, attrs: Map(declName -> Set(attr tokens)) }
// only the plain `mp` / `mpr` / `comm` tokens: with a parity (`comm 2`, `mp 4`) the generated lemma's hypotheses differ

function declAttrs(abs) {
    let st;
    try { st = fs.statSync(abs); } catch { return null; }
    const hit = cache.get(abs);
    if (hit && hit.mtimeMs === st.mtimeMs) return hit.attrs;
    const attrs = new Map();
    const lines = fs.readFileSync(abs, 'utf8').split(/\r?\n/);
    let pending = null;
    for (const l of lines) {
        const a = /^@\[([^\]]*)\]\s*$/.exec(l);
        if (a) { pending = a[1]; continue; }
        const d = /^(?:(?:private|protected|noncomputable)\s+)*(?:lemma|theorem)\s+([^\s:({[]+)/.exec(l);
        if (d) {
            if (pending != null) attrs.set(d[1], new Set(pending.split(',').map((s) => s.trim().replace(/\s+/g, ' '))));
            pending = null;
        } else if (l.trim() && !/^\s*--/.test(l) && !/^\/--/.test(l)) {
            if (!/^@\[/.test(l)) pending = null;
        }
    }
    cache.set(abs, { mtimeMs: st.mtimeMs, attrs });
    return attrs;
}

/** resolve a cited name like `A.is.B` / `A.is.B.left` / `S.A.is.B` to { abs, decl } through the imports */
function resolve(ctx, cited) {
    const { imports, opened } = ctx.scan;
    for (const { module } of imports) {
        const parts = module.split('.');
        if (parts.length < 3 || parts[0] !== 'Lemma') continue;
        const S = parts[1];
        const rest = parts.slice(2).join('.');
        const candidates = [`${S}.${rest}`];
        if (opened.has(S)) candidates.push(rest);
        for (const c of candidates) {
            let decl = null;
            if (cited === c) decl = 'main';
            else if (cited.startsWith(`${c}.`) && !cited.slice(c.length + 1).includes('.')) decl = cited.slice(c.length + 1);
            if (!decl) continue;
            return { abs: path.join(ctx.root, 'Lemma', S, ...parts.slice(2)) + '.lean', decl, rest };
        }
    }
    return null;
}

/** `A.is.B` (+ `.of.…`) → generated name of @[mp] (`B.of.A`) / @[mpr] (`A.of.B`), only for the plain form */
function generated(rest, kind) {
    const m = /^([^.]+)\.(is|eq)\.([^.]+)((?:\.of\..+)?)$/.exec(rest);
    if (!m) return null;
    const [, lhs, rel, rhs, of] = m;
    if (kind === 'mp') return rel === 'is' ? (of ? `${rhs}.of.${lhs}.${of.slice(4)}` : `${rhs}.of.${lhs}`) : null;
    if (kind === 'mpr') return rel === 'is' ? (of ? `${lhs}.of.${rhs}.${of.slice(4)}` : `${lhs}.of.${rhs}`) : null;
    if (kind === 'comm') return `${rhs}.${rel}.${lhs}${of}`;
    return null;
}

export function attrRules(ctx) {
    if (!ctx.root) return;
    const { P } = ctx;
    for (const d of ctx.decls) {
        if (!d.sig?.assign) continue;
        for (let i = d.sig.assign.line; i < d.end; i++) {
            const l = P.code[i];
            const re = /(←\s*)?(?<![\p{L}\p{N}_'.])((?:[\p{L}_][\p{L}\p{N}_'₀-₉]*\.)+(?:is|eq)(?:\.[\p{L}\p{N}_'₀-₉]+)+)/gu;
            let m;
            while ((m = re.exec(l))) {
                let name = m[2];
                let suffix = null;
                const sm = /\.(mp|mpr|symm)$/.exec(name);
                if (sm) { suffix = sm[1]; name = name.slice(0, -sm[0].length); }
                const back = !!m[1];
                if (!suffix && !back) continue;
                const r = resolve(ctx, name);
                if (!r) continue;
                const attrs = declAttrs(r.abs)?.get(r.decl);
                if (!attrs) continue;
                const col = m.index + (m[1]?.length ?? 0) + 1;
                if ((suffix === 'mp' || suffix === 'mpr') && attrs.has(suffix)) {
                    const g = r.decl === 'main' ? generated(r.rest, suffix) : null;
                    ctx.warn('attr-mp', i + 1, col, `\`${name}\` is tagged @[${suffix}]: use the generated lemma${g ? ` \`${g}\`` : ''} instead of \`${name}.${suffix}\``);
                } else if ((suffix === 'symm' || (back && !suffix)) && attrs.has('comm')) {
                    const g = r.decl === 'main' ? generated(r.rest, 'comm') : null;
                    ctx.warn('attr-comm', i + 1, col, `\`${name}\` is tagged @[comm]: use the generated lemma${g ? ` \`${g}\`` : ''} instead of \`${back ? '← ' : ''}${name}${suffix ? '.symm' : ''}\``);
                }
            }
        }
    }
}
