/**
 * `/lean/website/` plus `website/md` (PATH_INFO).
 */
import fs from 'fs/promises';
import path from 'path';
import { createRequire } from 'module';
import katex from 'katex';
import { REPO_ROOT } from './modulePath.mjs';

const require = createRequire(import.meta.url);
const marked = require('marked');

const MD_ROOT = path.join(REPO_ROOT, 'md');

function escapeHtml(s) {
  return String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

export function resolveWebsiteLang(req) {
  const q = req.query?.lang;
  if (typeof q === 'string' && q.trim() !== '') {
    const base = q.trim().split(/[-_]/)[0];
    return base || 'zh';
  }
  const accept = req.get('accept-language');
  if (!accept || accept.length <= 1) return 'zh';
  const langue = {};
  for (const raw of accept.split(',')) {
    const val = raw.trim();
    const m = val.match(/^([^;]+)(?:;q=([0-9.]+))?$/i);
    if (m) {
      const key = m[1].trim();
      const qv = m[2] != null ? parseFloat(m[2]) : 1.0;
      if (Number.isFinite(qv)) langue[key] = qv;
    }
  }
  let best = 'zh';
  let qval = -1;
  for (const [key, value] of Object.entries(langue)) {
    if (value > qval) {
      qval = value;
      best = key;
    }
  }
  const hy = best.indexOf('-');
  if (hy >= 0) return best.slice(0, hy);
  return best;
}

export function resolveWebsiteSection(req) {
  const s = req.query?.section;
  if (typeof s === 'string' && s.trim() !== '' && !s.includes('..') && !s.includes('/')) {
    return s.trim();
  }
  return 'home';
}

export function websiteLabels(lang) {
  switch (lang) {
    case 'zh':
      return {
        title: '算法形式化定理库',
        home: '网站主页',
        faq: '常见问题',
        bugReport: '故障报告',
        userGuide: '用户指南',
        participation: '项目参与',
        contact: '联系作者',
        endeavour: '我的奋斗',
        designManual: '设计文档',
        languageSelect: '选择语言',
        history: '探索历程',
        userManual: '操作手册',
        programmingReference: '编程参考',
      };
    default:
      return {
        title: 'Formalized Algorithmic Theorem Library',
        home: 'Home',
        faq: 'Frequently Asked Questions',
        bugReport: 'Bug Report',
        userGuide: 'User Guide',
        participation: 'Participation',
        contact: 'Contact Us',
        endeavour: 'Lifelong Endeavour',
        designManual: 'Design Manual',
        languageSelect: 'Select Language',
        history: 'Breif History',
        userManual: 'User Manual',
        programmingReference: 'Programming Reference',
      };
  }
}

const HOME_LANGS = ['en', 'zh', 'fr'];

/** Shared by every language version of `home.md`. */
export const HOME_FOOTER_HTML = [
  '<img src="website/png/national_emblem.png" alt="">',
  '<a href="http://www.beian.gov.cn/portal/registerSystemInfo?recordcode=33060202000937"><span>浙公网安备33060202000937号</span></a>',
  '<a href="https://beian.miit.gov.cn/"><span>浙ICP备20017509号-3</span></a>',
].join('\n');

/** Fills `#count` and `#lines` after the landing page is mounted. Paths are relative to `/lean/`. */
export const HOME_COUNT_SCRIPT = `
const count = document.querySelector('#count');
const lines = document.querySelector('#lines');
if (count)
  count.textContent = await get('request/count');
if (lines)
  lines.textContent = await get('request/lines');
`;

/**
 * First supported language in the browser's `Accept-Language` list.
 * @param {string | undefined} accept
 * @returns {'en' | 'zh' | 'fr'}
 */
export function homeLangFromAccept(accept) {
  if (!accept) return 'en';
  const ranked = [];
  for (const raw of accept.split(',')) {
    const match = raw.trim().match(/^([^;]+)(?:;q=([0-9.]+))?$/i);
    if (!match) continue;
    const base = match[1].trim().toLowerCase().split('-')[0];
    const q = match[2] != null ? parseFloat(match[2]) : 1;
    if (!HOME_LANGS.includes(base) || !Number.isFinite(q) || q <= 0) continue;
    ranked.push({ base, q });
  }
  ranked.sort((a, b) => b.q - a.q);
  return ranked[0]?.base || 'en';
}

/**
 * Home page in the requested language, from its first heading down.
 * The beian block is separate so the search page can pin it to the bottom.
 * @param {'en' | 'zh' | 'fr'} [lang]
 * @returns {Promise<{ home: string, footer: string }>}
 */
export async function homeLandingHtml(lang = 'en') {
  const folder = HOME_LANGS.includes(lang) ? lang : 'en';
  const file = path.join(MD_ROOT, folder, 'home.md');
  const text = await fs.readFile(file, 'utf8');
  const heading = text.search(/^# /m);
  const start = heading < 0 ? 0 : heading;
  const prose = text.slice(start)
    .replace(/<script[\s\S]*?<\/script>/g, '')
    .replace(/\]\(\.\.\/\?/g, '](?')
    // A dash line right after `<br>` is a setext heading underline, not a rule.
    .replace(/([^\n])\n([-*_]{3,})(?=\n)/g, '$1\n\n$2')
    .trim();
  return { home: marked(prose), footer: HOME_FOOTER_HTML, countScript: HOME_COUNT_SCRIPT };
}

/**
 * Turn a Markdown paper into HTML. Math is taken out before `marked` so
 * underscores stay in the formula, then drawn with KaTeX.
 * Delimiters are `\(...\)` and `\[...\]`, including multiline display math.
 * @param {string} source
 * @param {string} title
 * @returns {string} article inner HTML, title heading included
 */
export function renderMarkdownDocument(source, title) {
  const codes = [];
  const holdCode = (block) => {
    const token = `CODEPLACEHOLDER${codes.length}X`;
    codes.push(block);
    return token;
  };
  let text = String(source)
    .replace(/```[\s\S]*?```/g, holdCode)
    .replace(/`[^`\n]*`/g, holdCode);
  const slots = [];
  const holdMath = (latex, display) => {
    const token = `MATHPLACEHOLDER${slots.length}X`;
    slots.push({ latex: latex.trim(), display });
    return token;
  };
  text = text
    .replace(/\\\[([\s\S]*?)\\\]/g, (_, latex) => holdMath(latex, true))
    .replace(/\\\(([\s\S]*?)\\\)/g, (_, latex) => holdMath(latex, false));
  // Papers use `#` for sections. The filename is the document title.
  text = text.replace(/^(#{1,6}) /gm, (_, hashes) => `${hashes}# `);
  text = text
    .replace(/CODEPLACEHOLDER(\d+)X/g, (_, i) => codes[Number(i)])
    .replace(/([^\n])\n([-*_]{3,})(?=\n)/g, '$1\n\n$2');
  let html = marked(text);
  html = html.replace(/MATHPLACEHOLDER(\d+)X/g, (_, i) => {
    const slot = slots[Number(i)];
    if (!slot) return '';
    // KaTeX has no `@{…}` column glue. `{c@{\qquad}c}` is the two-branch
    // diagram; drop the glue so the array still renders.
    // `P_\hat\pi` is not a subscript: `\hat` needs a brace, as in `P_{\hat\pi}`.
    const latex = slot.latex
      .replace(/@\{[^{}]*\}/g, '')
      .replace(/_\\hat\s*(\\[a-zA-Z]+|\{[^{}]*\})/g, '_{\\hat$1}');
    return katex.renderToString(latex, {
      displayMode: slot.display,
      throwOnError: false,
      strict: 'ignore',
    });
  });
  return `<h1>${escapeHtml(title)}</h1>\n${html}`;
}

/**
 * Browser GET of a Markdown file under `/md/` returns HTML with KaTeX.
 * `en|zh|fr/home.md` stays raw: the landing page and the website shell read that source.
 */
export async function handleArxivMarkdown(req, res, next) {
  if (req.method !== 'GET' && req.method !== 'HEAD') return next();
  let rel = req.path || '/';
  try {
    rel = decodeURIComponent(rel);
  } catch {
    return next();
  }
  if (!rel.startsWith('/')) rel = `/${rel}`;
  const relFile = rel.replace(/^\/+/, '');
  if (!/\.md$/i.test(relFile) || rel.includes('..')) return next();
  if (/^(en|zh|fr)\/home\.md$/i.test(relFile)) return next();
  const abs = path.resolve(MD_ROOT, `.${rel}`);
  const root = path.resolve(MD_ROOT);
  if (abs !== root && !abs.startsWith(`${root}${path.sep}`)) {
    res.status(400).type('html').send('<p>Bad path</p>');
    return;
  }
  let source;
  try {
    source = await fs.readFile(abs, 'utf8');
  } catch {
    return next();
  }
  const title = path.basename(abs, '.md');
  const userSegment = req.params.userSegment || path.basename(REPO_ROOT);
  const body = renderMarkdownDocument(source, title);
  res.set('Content-Type', 'text/html; charset=utf-8');
  if (process.env.NODE_ENV !== 'production') res.set('Cache-Control', 'no-store');
  res.render('markdown', { title, userSegment, body });
}

/**
 * GET `/md/` and `/md/<dir>/` lists that directory. Files fall through
 * to the arXiv HTML renderer or to static serving.
 */
export async function handleMdListing(req, res, next) {
  if (req.method !== 'GET' && req.method !== 'HEAD') return next();
  let rel = req.path || '/';
  try {
    rel = decodeURIComponent(rel);
  } catch {
    return next();
  }
  if (!rel.startsWith('/')) rel = `/${rel}`;
  if (rel.includes('..') || rel.includes('\0')) return next();
  const relDir = rel.replace(/^\/+|\/+$/g, '');
  const abs = path.resolve(MD_ROOT, relDir);
  const root = path.resolve(MD_ROOT);
  if (abs !== root && !abs.startsWith(`${root}${path.sep}`)) {
    res.status(400).type('html').send('<p>Bad path</p>');
    return;
  }
  let stat;
  try {
    stat = await fs.stat(abs);
  } catch {
    return next();
  }
  if (!stat.isDirectory()) return next();

  const entries = await fs.readdir(abs, { withFileTypes: true });
  const rows = entries
    .filter((ent) => ent.name !== '.' && ent.name !== '..' && !ent.name.startsWith('.'))
    .map((ent) => ({ name: ent.name, dir: ent.isDirectory() }))
    .sort((a, b) => Number(b.dir) - Number(a.dir) || a.name.localeCompare(b.name));

  const userSegment = req.params.userSegment || path.basename(REPO_ROOT);
  const link = (relPath, dir) => {
    const encoded = relPath.split('/').filter(Boolean).map((part) => encodeURIComponent(part)).join('/');
    if (!encoded) return `/${userSegment}/md/`;
    return `/${userSegment}/md/${encoded}${dir ? '/' : ''}`;
  };
  const parent = relDir
    ? link(relDir.split('/').slice(0, -1).join('/'), true)
    : '';
  const list = rows.map((row) => {
    const child = relDir ? `${relDir}/${row.name}` : row.name;
    return { href: link(child, row.dir), label: row.dir ? `${row.name}/` : row.name };
  });
  const title = relDir ? `md/${relDir}` : 'md';
  res.set('Content-Type', 'text/html; charset=utf-8');
  if (process.env.NODE_ENV !== 'production') res.set('Cache-Control', 'no-store');
  res.render('mdList', { title, parent, rows: list });
}

export function renderWebsiteIndex(req, res) {
  const lang = resolveWebsiteLang(req);
  const section = resolveWebsiteSection(req);
  const labels = websiteLabels(lang);
  // Relative `style.css` / `../js/…` / `../website/md/…` need a directory base.
  // Without this, `/lean/website` (no trailing slash) resolves assets under `/lean/` and breaks.
  // Express does not redirect to a trailing slash, because some proxies strip `/` and would loop.
  const userSegment = req.params.userSegment || path.basename(REPO_ROOT);
  res.set('Content-Type', 'text/html; charset=utf-8');
  if (process.env.NODE_ENV !== 'production') {
    res.set('Cache-Control', 'no-store');
  }
  res.render('website', { lang, section, userSegment, ...labels });
}

/**
 * Mounted at `/lean/website/md`; `req.url` is PATH_INFO remainder (e.g. `/zh/home.md`).
 */
export async function handleWebsiteMd(req, res) {
  let pathInfo = req.url.split('?')[0];
  if (!pathInfo || pathInfo === '' || pathInfo === '/') {
    pathInfo = '/';
  } else if (!pathInfo.startsWith('/')) {
    pathInfo = `/${pathInfo}`;
  }

  if (/^\/(\w+)\/.+\.md$/.test(pathInfo)) {
    const m = pathInfo.match(/^\/(\w+)\//);
    const lang = m ? m[1] : 'en';
    const title = lang === 'zh' ? '标记文档' : 'MarkDown Documents';
    const userSegment = req.params.userSegment ?? path.basename(REPO_ROOT);
    const fetchPath = `/${userSegment}/md${pathInfo}`;
    res.set('Content-Type', 'text/html; charset=utf-8');
    if (process.env.NODE_ENV !== 'production') {
      res.set('Cache-Control', 'no-store');
    }
    res.render('websiteMdViewer', { title, fetchPath, userSegment });
    return;
  }

  const relDir = pathInfo === '/' ? '' : pathInfo.replace(/^\/+/, '');
  const diskPath = path.join(MD_ROOT, relDir);
  const resolvedMd = path.resolve(MD_ROOT);
  const resolved = path.resolve(diskPath);
  if (!resolved.startsWith(resolvedMd)) {
    res.status(400).type('html').send('<p>Bad path</p>');
    return;
  }

  let entries;
  try {
    entries = await fs.readdir(resolved, { withFileTypes: true });
  } catch {
    res.status(404).type('html').send('<p>Not found</p>');
    return;
  }

  const parts = ['<!DOCTYPE html><meta charset="utf-8"><title>md</title>'];
  for (const ent of entries) {
    const name = ent.name;
    if (name === '.' || name === '..') continue;
    const full = path.join(resolved, name);
    if (ent.isDirectory()) {
      const mdSibling = `${full}.md`;
      try {
        await fs.access(mdSibling);
        continue;
      } catch {
        /* list the directory */
      }
    }
    const nextRel = relDir ? `${relDir}/${name}` : name;
    const href = `/lean/website/md/${nextRel}`;
    parts.push(`<a href="${escapeHtml(href)}">${escapeHtml(name)}</a><br><br>`);
  }
  res.type('html').send(parts.join('\n'));
}
