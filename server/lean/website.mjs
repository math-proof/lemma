/**
 * Mirrors PHP `lean.php/website` → Node `/lean/website/` plus `website/md.php` (PATH_INFO).
 */
import fs from 'fs/promises';
import path from 'path';
import { REPO_ROOT } from './modulePath.mjs';

const MD_ROOT = path.join(REPO_ROOT, 'website', 'md');

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

export function renderWebsiteIndex(req, res) {
  const lang = resolveWebsiteLang(req);
  const section = resolveWebsiteSection(req);
  const labels = websiteLabels(lang);
  res.set('Content-Type', 'text/html; charset=utf-8');
  if (process.env.NODE_ENV !== 'production') {
    res.set('Cache-Control', 'no-store');
  }
  res.render('website', { lang, section, ...labels });
}

/**
 * Mounted at `/lean/website/md.php`; `req.url` is PATH_INFO remainder (e.g. `/zh/home.md`).
 */
export async function handleWebsiteMdPhp(req, res) {
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
    const fetchPath = `/lean/website/md${pathInfo}`;
    res.set('Content-Type', 'text/html; charset=utf-8');
    if (process.env.NODE_ENV !== 'production') {
      res.set('Cache-Control', 'no-store');
    }
    res.render('websiteMdViewer', { title, fetchPath });
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
        /* list dir link like PHP */
      }
    }
    const nextRel = relDir ? `${relDir}/${name}` : name;
    const href = `/lean/website/md.php/${nextRel}`;
    parts.push(`<a href="${escapeHtml(href)}">${escapeHtml(name)}</a><br><br>`);
  }
  res.type('html').send(parts.join('\n'));
}
