/**
 * File-level rules: `open` statements, attribute docstring table, `-- created on` / `-- updated on` dates.
 */
import fs from 'node:fs';
import path from 'node:path';

/**
 * Top-level `import` / `open` / `namespace` commands of a Lean file.
 * `opened`: names opened by a plain / selective / `in` open or a `namespace` (for `open-section`);
 * `plainOpens`: every plain `open … X …` entry ({ name, line, selective, scoped, local }) for `open-duplicate`.
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

/**
 * `header-spacing`: top-level `import` / `open` / `set_option` form one contiguous preamble
 * (no blank lines inside), then exactly two blank lines before the rest of the file
 * (`/--`, `@[…]`, `namespace`, the lemma, …).
 *
 * ```
 * import …          -- contiguous
 * open …            -- no blank between import and open
 *
 *                   -- exactly two blanks
 * /--
 * ```
 */
export function headerSpacing(ctx) {
    const { raw } = ctx.P;
    const isCmd = (s) => /^(import|open|set_option)\b/.test(s);
    const isCont = (s) => /^\s+\S/.test(s); // indented continuation of a multi-line `open`
    // preamble = leading run of cmds / blanks / open-continuations, stopped by any other non-blank
    let i = 0;
    const cmds = []; // 0-based line indices of preamble commands (and their continuations)
    while (i < raw.length) {
        const s = raw[i];
        if (isCmd(s)) {
            cmds.push(i);
            i++;
            while (i < raw.length && isCont(raw[i])) {
                cmds.push(i);
                i++;
            }
            continue;
        }
        if (/^\s*$/.test(s)) {
            i++;
            continue;
        }
        break;
    }
    if (!cmds.length) return;
    const first = cmds[0];
    const last = cmds[cmds.length - 1];
    // blank line(s) between preamble commands
    for (let k = first; k < last; k++) {
        if (/^\s*$/.test(raw[k]) && !cmds.includes(k)) {
            ctx.warn(
                'header-spacing',
                k + 1,
                1,
                'no blank line between `import` / `open` / `set_option`; keep the preamble contiguous',
            );
            break; // one finding for the internal gap
        }
    }
    // trailing blanks after the last preamble command, before the next non-blank
    let j = last + 1;
    let blanks = 0;
    while (j < raw.length && /^\s*$/.test(raw[j])) {
        blanks++;
        j++;
    }
    // no body after the preamble (empty / preamble-only file): skip the trailer check
    if (j >= raw.length) return;
    if (blanks !== 2) {
        ctx.warn(
            'header-spacing',
            last + 1,
            1,
            `exactly two blank lines after the preamble before the rest of the file (got ${blanks})`,
        );
    }
}

/**
 * `max-heartbeats`: `set_option maxHeartbeats N` with N >= 1_000_000.
 * The warning asks to try half; it does not change the file.
 */
export function maxHeartbeats(ctx) {
    const { raw } = ctx.P;
    for (let i = 0; i < raw.length; i++) {
        const m = /(?:^|\s)set_option maxHeartbeats (\d+)\b/.exec(raw[i]);
        if (!m) continue;
        const n = Number(m[1]);
        if (!(n >= 1_000_000)) continue;
        ctx.warn(
            'max-heartbeats',
            i + 1,
            m.index + 1,
            `maxHeartbeats ${n} is not strictly below 1000000; try ${Math.floor(n / 2)}`,
        );
    }
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
 * `open-duplicate`: the same name listed twice in plain top-level opens.
 */
export function openDuplicate(ctx) {
    const { openEntries } = ctx.scan;
    const seen = new Map();
    for (const e of openEntries) {
        if (e.scoped || e.selective || e.local) continue;
        if (seen.has(e.name)) {
            ctx.warn('open-duplicate', e.line, null, `\`${e.name}\` is already opened on line ${seen.get(e.name)}; drop the duplicate`);
            continue;
        }
        seen.set(e.name, e.line);
    }
}
/**
 * `open-merge`: consecutive plain (or consecutive `scoped`) top-level `open` commands
 * should be one `open A B C …` (resp. `open scoped A B C …`). Only blank lines may sit
 * between them; a comment, `import`, `set_option`, selective/`in` open, or a different
 * open kind breaks the run. Suggests the merged line.
 */
export function openMerge(ctx) {
    const { raw, code: lines } = ctx.P;
    /** @type {{ start: number, end: number, kind: string, names: string[], code: string }[]} */
    const cmds = [];
    for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        if (!/^open\b/.test(line)) continue;
        const start = i;
        let text = line.replace(/^open\b/, '');
        while (i + 1 < lines.length && /^\s+\S/.test(lines[i + 1])) text += ` ${lines[++i]}`;
        text = text.trim();
        const sc = /^scoped\b/.exec(text);
        if (sc) text = text.slice(sc[0].length).trim();
        const isIn = /\bin\s*$/.test(text);
        const tail = /\b(hiding|renaming)\b/.exec(text);
        const head = tail ? text.slice(0, tail.index) : text;
        const body = head.replace(/\bin\s*$/, ' ');
        const names = [];
        let selective = false;
        const re = /([^\s()]+)(\s*\([^()]*\))?/g;
        let e;
        while ((e = re.exec(body))) {
            names.push(e[1]);
            if (e[2]) selective = true;
        }
        // kind: plain | scoped | other (selective / local — never merge)
        let kind = 'other';
        if (!selective && !isIn && !tail) kind = sc ? 'scoped' : 'plain';
        cmds.push({ start, end: i, kind, names, code: raw[start] });
    }
    // runs of same mergeable kind with only blank lines between commands
    let run = [];
    const flush = () => {
        if (run.length < 2) {
            run = [];
            return;
        }
        const kind = run[0].kind;
        const names = run.flatMap((c) => c.names);
        const merged =
            kind === 'scoped'
                ? `open scoped ${names.join(' ')}`
                : `open ${names.join(' ')}`;
        const first = run[0];
        ctx.warn(
            'open-merge',
            first.start + 1,
            1,
            `merge ${run.length} consecutive \`open\` commands into one: \`${merged}\``,
            { suggested: merged },
        );
        run = [];
    };
    for (let k = 0; k < cmds.length; k++) {
        const c = cmds[k];
        if (c.kind === 'other' || !c.names.length) {
            flush();
            continue;
        }
        if (!run.length) {
            run = [c];
            continue;
        }
        const prev = run[run.length - 1];
        // only blanks between previous command end and this start
        let onlyBlanks = true;
        for (let j = prev.end + 1; j < c.start; j++) {
            if (!/^\s*$/.test(raw[j])) {
                onlyBlanks = false;
                break;
            }
        }
        if (onlyBlanks && c.kind === prev.kind) {
            run.push(c);
        } else {
            flush();
            run = [c];
        }
    }
    flush();
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
 * `attr-docstring`: `@[path, <other attrs>]` on `lemma main` without the `/-- | attributes | lemma | … -/` table
 * (exactly the precondition of `py/docstring.py`).
 */
const CUSTOM_ATTR_HEADS = new Set([
    'main', 'comm', 'mp', 'mpr', 'mp.comm', 'mpr.comm', 'comm.is', 'is.comm',
    'mt', 'mp.mt', 'mpr.mt', 'Or.inl', 'Or.inr', 'mpr.left', 'mpr.right', 'mp.left', 'mp.right',
    'And.left', 'And.right', 'fin', 'fin.comm', 'fin.mp', 'fin.mpr', 'val', 'Fun', 'subst', 'cast', 'cast.fin',
    'mp and', 'mpr and', 'mp.comm and', 'mpr.comm and',
]); // = py/docstring.py CUSTOM_ATTR_HEADS

/** Strip Lean «» escapes so keyword attrs like «fun» match CUSTOM_ATTR_HEADS. */
function attrHeadToken(t) {
    if (/^(mp|mpr|mp\.comm|mpr\.comm) and$/.test(t)) return t;
    const head = t.split(/\s+/)[0];
    if (head.startsWith('«') && head.endsWith('»') && head.length >= 2) return head.slice(1, -1);
    return head;
}

export function attrDocstring(ctx) {
    const src = ctx.source.replace(/\r\n?/g, '\n');
    const re = /@\[main,\s*([^\]]+)\]\s*\nprivate lemma main\b/g;
    let m;
    while ((m = re.exec(src))) {
        const custom = m[1].split(',').map((t) => t.trim()).filter(Boolean)
            .map(attrHeadToken)
            .filter((t) => t !== 'main' && CUSTOM_ATTR_HEADS.has(t));
        if (!custom.length) continue;
        const before = src.slice(0, m.index);
        if (/\/--\s*\n\| attributes \| lemma \|[\s\S]*?\n-\/\s*\n+$/.test(before)) continue;
        const line = before.split('\n').length;
        ctx.warn('attr-docstring', line, 1,
            `\`@[path, ${m[1].trim()}]\` has no attribute docstring table; run \`python py/docstring.py ${ctx.file ?? '<file>'}\``);
    }
}

const ymd = (d) => `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`;

/**
 * Dates (`-- created on YYYY-MM-DD`, `-- updated on YYYY-MM-DD`, at the end of every lemma file):
 *   `date-created-missing`, `date-updated-same` (updated == created ⇒ omit it), `date-order` (updated before created,
 *   or a date in the future), `date-created-today` (only for a truly new git file: untracked/added with no matching lemma move, `ctx.isNew`),
 *   `date-spacing` (exactly two blank lines before `-- created on`).
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
    // exactly two blank lines before `-- created on` (after the proof / last body line)
    {
        const idx = created.line - 1; // 0-based
        let j = idx - 1;
        let blanks = 0;
        while (j >= 0 && /^\s*$/.test(raw[j])) {
            blanks++;
            j--;
        }
        // skip when `-- created on` is at the top of the file (no preceding body)
        if (j >= 0 && blanks !== 2) {
            ctx.warn(
                'date-spacing',
                created.line,
                1,
                `exactly two blank lines before \`-- created on\` (got ${blanks})`,
            );
        }
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

/**
 * `decl-keyword-dir` (text fallback; the AST rule in `astRules.mjs` reads the keyword from the node class):
 * `theorem` in a `Lemma/` file. `ctx.decls` comes from the comment/string-blanked source and only matches the keyword
 * at the start of a declaration line (after `@[…]` / modifiers).
 */
export function declKeywordDirText(ctx) {
    if (ctx.astCovered.has('decl-keyword-dir')) return;
    if (!/(^|\/)Lemma\//.test(String(ctx.file ?? '').replace(/\\/g, '/'))) return;
    for (const d of ctx.decls) {
        if (d.kind !== 'theorem') continue;
        ctx.warn('decl-keyword-dir', d.line + 1, 1, `\`theorem${d.name ? ` ${d.name}` : ''}\` in \`Lemma/\`: declare it with \`lemma\``);
    }
}

/**
 * `blank-sublemmas`: consecutive `private lemma` declarations must be separated by
 * exactly one blank line (not two or more). Doc comments `/-- … -/` and `@[…]` on the
 * next sublemma count as its lead; blanks inside a proof are out of scope.
 */
export function blankSublemmas(ctx) {
    const { P, decls } = ctx;
    const { raw } = P;

    const isPrivateLemma = (d) =>
        d.kind === 'lemma' && /\bprivate\b/.test(P.code[d.line] ?? '');

    /** 0-based first line of decl lead: optional `/-- … -/` (or `/- … -/`), then `@[…]`, then keyword. */
    const leadStart = (d) => {
        let i = d.attrLine >= 0 ? d.attrLine : d.line;
        let j = i - 1;
        while (j >= 0 && /^\s*$/.test(raw[j])) j--;
        if (j < 0 || !raw[j].includes('-/')) return i;
        // Walk characters backward from this line to the matching `/-` opener.
        const text = raw.slice(0, j + 1).join('\n');
        let pos = text.length - 1;
        while (pos > 0 && !(text[pos - 1] === '-' && text[pos] === '/')) pos--;
        if (pos <= 0) return i;
        let depth = 1;
        pos -= 2;
        while (pos >= 0 && depth > 0) {
            if (pos > 0 && text[pos - 1] === '-' && text[pos] === '/') {
                depth++;
                pos -= 2;
                continue;
            }
            if (pos > 0 && text[pos - 1] === '/' && text[pos] === '-') {
                depth--;
                pos -= 2;
                continue;
            }
            pos--;
        }
        // `pos + 1` is the start of the opening `/-`; convert to line index.
        const startLine = text.slice(0, Math.max(0, pos + 1)).split('\n').length - 1;
        return Math.min(startLine, i);
    };

    for (let k = 0; k + 1 < decls.length; k++) {
        const a = decls[k];
        const b = decls[k + 1];
        if (!isPrivateLemma(a) || !isPrivateLemma(b)) continue;
        const head = leadStart(b);
        if (head <= a.end) continue;
        let blanks = 0;
        let secondBlank = null;
        let pure = true;
        for (let i = a.end; i < head; i++) {
            if (/^\s*$/.test(raw[i])) {
                blanks++;
                if (blanks === 2) secondBlank = i;
            } else {
                pure = false;
                break;
            }
        }
        if (!pure || blanks < 2) continue;
        const n = blanks;
        ctx.warn(
            'blank-sublemmas',
            (secondBlank ?? a.end) + 1,
            1,
            n === 2
                ? 'two blank lines between sublemmas; use one'
                : `${n} blank lines between sublemmas; use one`,
        );
    }
}


/**
 * `lemma-namespace`: on Lemma/ files, ban top-level `namespace` / `section` / `variable(s)`.
 * Comments/strings are blanked by prepare, so `-- namespace …` is clean. Non-Lemma files skip.
 */
export function lemmaNamespace(ctx) {
    if (!ctx.isLemmaFile) return;
    const { P } = ctx;
    for (let i = 0; i < P.code.length; i++) {
        const line = P.code[i];
        let kind = null;
        if (/^namespace\s+\S/.test(line)) kind = 'namespace';
        else if (/^section\s+\S/.test(line)) kind = 'section';
        else if (/^variables\b/.test(line)) kind = 'variables';
        else if (/^variable\b/.test(line)) kind = 'variable';
        if (!kind) continue;
        const shown = (P.raw[i] ?? '').trim();
        ctx.warn(
            'lemma-namespace',
            i + 1,
            1,
            `\`${shown}\`: ${kind} within Lemma is not allowed`,
        );
    }
}
