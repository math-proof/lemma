/**
 * File-level rules: `open` statements, attribute docstring table, `-- created on` / `-- updated on` dates.
 */
import fs from 'node:fs';
import path from 'node:path';

/**
 * Top-level `import` / `open` / `namespace` commands of a Lean file.
 * `opened`: names opened by a plain / selective / `in` open or a `namespace` (for `open-section`);
 * `plainOpens`: every plain `open … X …` entry ({ name, line, selective, scoped, local }) for `open-unused` / `open-duplicate`.
 */
export function scanImportsAndOpens(P) {
    const { raw, code: lines } = P;
    const imports = [];
    const opened = new Set();
    const scoped = new Set();
    const namespaces = new Set();
    const openEntries = [];
    for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        let m = /^import\s+(\S+)/.exec(line);
        if (m) {
            imports.push({ module: m[1], line: i + 1, code: raw[i] });
            continue;
        }
        m = /^namespace\s+(\S+)/.exec(line);
        if (m) {
            const parts = m[1].split('.');
            for (let k = 1; k <= parts.length; k++) {
                opened.add(parts.slice(0, k).join('.'));
                namespaces.add(parts.slice(0, k).join('.'));
            }
            continue;
        }
        if (!/^open\b/.test(line)) continue;
        const line0 = i;
        // an `open` command may continue on indented lines
        let text = line.replace(/^open\b/, '');
        while (i + 1 < lines.length && /^\s+\S/.test(lines[i + 1])) text += ` ${lines[++i]}`;
        text = text.trim();
        let target = opened;
        const sc = /^scoped\b/.exec(text);
        if (sc) {
            target = scoped;
            text = text.slice(sc[0].length);
        }
        const isIn = /\bin\s*$/.test(text);
        // entries in order, noting a selective `X (a b)` / `hiding` / `renaming` tail
        const tail = /\b(hiding|renaming)\b/.exec(text);
        const head = tail ? text.slice(0, tail.index) : text;
        const re = /([^\s()]+)(\s*\([^()]*\))?/g;
        let e;
        const body = head.replace(/\bin\s*$/, ' ');
        while ((e = re.exec(body))) {
            openEntries.push({ name: e[1], line: line0 + 1, selective: !!e[2], scoped: !!sc, local: isIn, code: raw[line0] });
        }
        text = text
            .replace(/\([^()]*\)/g, ' ') // `open X (a b)`: X is opened (selected names only)
            .replace(/\b(hiding|renaming)\b.*$/, ' ') // `open X hiding a` / `open X renaming a → b`
            .replace(/\bin\s*$/, ' '); // `open X in` (applies to the next command — the lemma here)
        for (const name of text.split(/\s+/)) if (name) target.add(name);
    }
    return { imports, opened, scoped, namespaces, openEntries };
}

/** `open-section`: imported `Lemma.X.…` but `X` is not opened */
export function openSection(ctx) {
    const { imports, opened } = ctx.scan;
    const seen = new Set();
    for (const { module, line } of imports) {
        const parts = module.split('.');
        if (parts.length < 3 || parts[0] !== 'Lemma') continue;
        const section = parts[1];
        if (!ctx.sections.has(section) || opened.has(section) || seen.has(section)) continue;
        seen.add(section);
        ctx.warn('open-section', line, 1, `forget to open ${section} since ${module} is imported`, { section, import: module });
    }
}

/**
 * `open-unused`: the static logic of `ps1/delete_open.ps1` / `sh/delete_open.sh` — a plain (not `scoped`, not selective)
 * `open … X …` of a section `X` while no `import Lemma.X.…` exists; additionally skipped when the file has
 * `namespace X` or the open is `open … in`.
 * `open-duplicate`: the same name listed twice in plain top-level opens.
 */
export function openUnusedAndDuplicate(ctx) {
    const { imports, namespaces, openEntries } = ctx.scan;
    const importedSections = new Set();
    for (const { module } of imports) {
        const parts = module.split('.');
        if (parts.length >= 3 && parts[0] === 'Lemma') importedSections.add(parts[1]);
    }
    const seen = new Map();
    for (const e of openEntries) {
        if (e.scoped || e.selective || e.local) continue;
        if (seen.has(e.name)) {
            ctx.warn('open-duplicate', e.line, null, `\`${e.name}\` is already opened on line ${seen.get(e.name)}; drop the duplicate`);
            continue;
        }
        seen.set(e.name, e.line);
        if (ctx.sections.has(e.name) && !importedSections.has(e.name) && !namespaces.has(e.name)) {
            ctx.warn('open-unused', e.line, null,
                `\`open ${e.name}\` but nothing from Lemma.${e.name} is imported; run \`pwsh ps1/delete_open.ps1 ${ctx.file ?? '<file>'}\` (or \`bash sh/delete_open.sh\`) or drop it`);
        }
    }
}


/**
 * `open-prefix`: a reference `Random.Foo.Bar` while `open Random`, when `Foo.Bar` resolves to a real lemma under
 * `Lemma/Random/…` and no other **open** section also declares that short path — drop the leading `Random.`.
 * Uses the filesystem layout of `Lemma/<Section>/…/*.lean` (same as imports). Attribute-generated names that have
 * no `.lean` file of their own are skipped (no warning).
 */
const lemmaRestCache = new Map(); // root -> Map(section -> Set("A.B.C"))

function lemmaRests(root, section) {
    let byRoot = lemmaRestCache.get(root);
    if (!byRoot) {
        byRoot = new Map();
        lemmaRestCache.set(root, byRoot);
    }
    if (byRoot.has(section)) return byRoot.get(section);
    const rests = new Set();
    const base = path.join(root, 'Lemma', section);
    const walk = (dir, parts) => {
        let entries;
        try { entries = fs.readdirSync(dir, { withFileTypes: true }); } catch { return; }
        for (const e of entries) {
            if (e.name.startsWith('.')) continue;
            if (e.isDirectory()) walk(path.join(dir, e.name), parts.concat(e.name));
            else if (e.isFile() && e.name.endsWith('.lean') && !e.name.endsWith('.echo.lean')) {
                const stem = e.name.slice(0, -'.lean'.length);
                rests.add(parts.concat(stem).join('.'));
            }
        }
    };
    walk(base, []);
    byRoot.set(section, rests);
    return rests;
}

export function openPrefix(ctx) {
    if (!ctx.root) return;
    const { namespaces, openEntries } = ctx.scan;
    const { P } = ctx;
    // sections brought into scope by a plain (non-selective, non-scoped) `open` or by `namespace`
    const isOpened = (s) => {
        if (namespaces.has(s)) return true;
        return openEntries.some((e) => e.name === s && !e.scoped && !e.selective);
    };
    const warnSecs = [...ctx.sections].filter(isOpened);
    if (!warnSecs.length) return;
    // ambiguity set = opened ∪ file's own Lemma/<Section>/ (even if not opened)
    const ambigSecs = new Set(warnSecs);
    if (ctx.file) {
        const m = ctx.file.replace(/\\/g, '/').match(/(?:^|\/)Lemma\/([^/]+)\//);
        if (m && ctx.sections.has(m[1])) ambigSecs.add(m[1]);
    }
    const restsOf = new Map([...ambigSecs].map((s) => [s, lemmaRests(ctx.root, s)]));
    const reported = new Set(); // `${line}:${section}.${short}` once
    for (const section of warnSecs) {
        const rests = restsOf.get(section);
        if (!rests?.size) continue;
        // `Random.Foo.Bar.Baz` — at least one segment after the section (a lemma path, not a bare name)
        const esc = section.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
        const re = new RegExp(
            `(?<![\\w.])${esc}\\.((?:[\\p{L}_][\\p{L}\\p{N}_'₀-₉]*\\.)+[\\p{L}_][\\p{L}\\p{N}_'₀-₉]*)`,
            'gu',
        );
        for (let i = 0; i < P.code.length; i++) {
            const line = P.code[i];
            let m;
            re.lastIndex = 0;
            while ((m = re.exec(line))) {
                const short = m[1];
                // must be a real lemma under this section
                if (!rests.has(short)) continue;
                // unambiguous among open (+ own) sections
                let owners = 0;
                for (const other of ambigSecs) {
                    if (restsOf.get(other)?.has(short)) owners++;
                }
                if (owners !== 1) continue;
                const key = `${i + 1}:${section}.${short}`;
                if (reported.has(key)) continue;
                reported.add(key);
                const full = `${section}.${short}`;
                ctx.warn(
                    'open-prefix',
                    i + 1,
                    m.index + 1,
                    `drop leading \`${section}.\`: \`${full}\` is unambiguous under \`open ${section}\` — write \`${short}\``,
                    { section, short, full, stmt: full },
                );
            }
        }
    }
}


/**
 * `attr-docstring`: `@[main, <other attrs>]` on `lemma main` without the `/-- | attributes | lemma | … -/` table
 * (exactly the precondition of `py/docstring.py`).
 */
const CUSTOM_ATTR_HEADS = new Set([
    'main', 'comm', 'mp', 'mpr', 'mp.comm', 'mpr.comm', 'comm.is', 'is.comm',
    'mt', 'mp.mt', 'mpr.mt', 'Or.inl', 'Or.inr', 'mpr.left', 'mpr.right', 'mp.left', 'mp.right',
    'And.left', 'And.right', 'fin', 'fin.comm', 'fin.mp', 'fin.mpr', 'val', 'subst', 'cast', 'cast.fin',
    'mp and', 'mpr and', 'mp.comm and', 'mpr.comm and',
]); // = py/docstring.py CUSTOM_ATTR_HEADS

export function attrDocstring(ctx) {
    const src = ctx.source.replace(/\r\n?/g, '\n');
    const re = /@\[main,\s*([^\]]+)\]\s*\nprivate lemma main\b/g;
    let m;
    while ((m = re.exec(src))) {
        const custom = m[1].split(',').map((t) => t.trim()).filter(Boolean)
            .map((t) => (/^(mp|mpr|mp\.comm|mpr\.comm) and$/.test(t) ? t : t.split(/\s+/)[0]))
            .filter((t) => t !== 'main' && CUSTOM_ATTR_HEADS.has(t));
        if (!custom.length) continue;
        const before = src.slice(0, m.index);
        if (/\/--\s*\n\| attributes \| lemma \|[\s\S]*?\n-\/\s*\n+$/.test(before)) continue;
        const line = before.split('\n').length;
        ctx.warn('attr-docstring', line, 1,
            `\`@[main, ${m[1].trim()}]\` has no attribute docstring table; run \`python py/docstring.py ${ctx.file ?? '<file>'}\``);
    }
}

const ymd = (d) => `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`;

/**
 * Dates (`-- created on YYYY-MM-DD`, `-- updated on YYYY-MM-DD`, at the end of every lemma file):
 *   `date-created-missing`, `date-updated-same` (updated == created ⇒ omit it), `date-order` (updated before created,
 *   or a date in the future), `date-created-today` (only for a file new to git: untracked or added, `ctx.isNew`).
 */
export function dates(ctx) {
    const { raw } = ctx.P;
    const today = ctx.today ?? ymd(new Date());
    let created = null;
    let updated = null;
    raw.forEach((l, i) => {
        let m = /^\s*--\s*created on\s+(\d{4}-\d{2}-\d{2})\s*$/.exec(l);
        if (m && !created) created = { date: m[1], line: i + 1 };
        m = /^\s*--\s*updated on\s+(\d{4}-\d{2}-\d{2})\s*$/.exec(l);
        if (m) updated = { date: m[1], line: i + 1 }; // the last one wins
    });
    if (!created) {
        if (ctx.isLemmaFile && ctx.decls.length) ctx.warn('date-created-missing', raw.length, null, `no \`-- created on ${today}\` line at the end of the file`);
        return;
    }
    if (updated && updated.date === created.date) {
        ctx.warn('date-updated-same', updated.line, 1, `\`updated on ${updated.date}\` equals the created date; delete this line`);
    } else if (updated && updated.date < created.date) {
        ctx.warn('date-order', updated.line, 1, `updated date ${updated.date} is before the created date ${created.date}`);
    }
    for (const d of [created, updated]) {
        if (d && d.date > today) ctx.warn('date-order', d.line, 1, `date ${d.date} is in the future (today is ${today})`);
    }
    if (ctx.isNew && created.date !== today) {
        ctx.warn('date-created-today', created.line, 1, `new file: the created date should be today, \`-- created on ${today}\``);
    }
}
