<template>
  <div
    :ref="$refs.explorerRoot"
    class="explorer"
    tabindex="0"
    @keydown.capture="onExplorerKeydown"
  >
    <searchForm
      v-if="issearch"
      :q="q"
      :caseSensitive="caseSensitive"
      :wholeWord="wholeWord"
      :regularExpression="regularExpression"
      :nlp="nlp"
      :fullText="fullText"
    />

    <header v-if="!issearch" class="explorer-toolbar">
      <div class="explorer-toolbar-row">
        <nav class="breadcrumb" aria-label="Path">
          <a class="crumb root">Lemma</a>
          <template v-for="(part, i) in breadcrumbParts" :key="i">
            <span class="crumb-sep" aria-hidden="true">›</span>
            <a
              class="crumb"
              :href="crumbHref(i)"
            >{{ part }}</a>
          </template>
        </nav>
        <div class="toolbar-search-area">
          <button
            v-if="!folderSearchOpen"
            type="button"
            class="toolbar-search-fab"
            title="Search in current folder (Ctrl+F)"
            aria-label="Open folder search"
            @click="openFolderSearch"
          >
            <svg class="toolbar-search-icon" viewBox="0 0 24 24" aria-hidden="true">
              <path fill="currentColor" d="M15.5 14h-.79l-.28-.27A6.471 6.471 0 0 0 16 9.5 6.5 6.5 0 1 0 9.5 16c1.61 0 3.09-.59 4.23-1.57l.27.28v.79l5 4.99L20.49 19l-4.99-5zm-6 0C7.01 14 5 11.99 5 9.5S7.01 5 9.5 5 14 7.01 14 9.5 11.99 14 9.5 14z"/>
            </svg>
          </button>
          <div
            v-else
            class="folder-search-panel"
            role="search"
          >
            <label class="folder-search-label" :for="folderSearchInputId">
              Search in {{ currentFolderLabel }}
            </label>
            <input
              :id="folderSearchInputId"
              :ref="$refs.folderSearchInputRef"
              v-model="folderSearchQuery"
              type="search"
              class="folder-search-input"
              spellcheck="false"
              autocomplete="off"
              :placeholder="`Search ${currentFolderLabel}`"
              @keydown.esc.prevent="closeFolderSearch"
            />
            <button
              type="button"
              class="folder-search-close"
              title="Close (Esc)"
              aria-label="Close folder search"
              @click="closeFolderSearch"
            >
              ×
            </button>
          </div>
        </div>
      </div>
    </header>

    <div v-if="!issearch" class="explorer-frame">
      <div class="col-header" role="row">
        <span class="col-name">Name</span>
        <span class="col-date">Date modified</span>
        <span class="col-type">Type</span>
        <span class="col-size">Size</span>
      </div>
      <ul
        class="item-list"
        role="listbox"
        :aria-activedescendant="activeId"
      >
        <li
          v-for="(row, idx) in displayRows"
          :id="'explorer-row-' + idx"
          :key="row.kind + ':' + row.name"
          class="item-row"
          :class="{ selected: idx === selectedIndex, focused: idx === selectedIndex }"
          role="option"
          :aria-selected="idx === selectedIndex"
          @click="selectRow(idx)"
        >
          <button
            type="button"
            class="row-inner"
            @dblclick.prevent="openRow(row)"
          >
            <span class="col-name cell-name">
              <span class="file-icon" :class="row.kind" aria-hidden="true">
                <svg v-if="row.kind === 'folder'" class="ico-svg" viewBox="0 0 32 24" fill="none">
                  <path d="M2 6h9l2 2h15v14H2V6z" fill="#F5C84C" stroke="#D4A017" stroke-width="1.2"/>
                  <path d="M2 8h28v12H2V8z" fill="#FFE69A" opacity=".9"/>
                </svg>
                <svg v-else class="ico-svg ico-lean" viewBox="0 0 24 28" fill="none" aria-hidden="true">
                  <path d="M6 2h12l4 4v20a2 2 0 0 1-2 2H6a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2z" fill="#f8f8f8" stroke="#6b6b6b" stroke-width="1"/>
                  <path d="M18 2v4h4" stroke="#6b6b6b" stroke-width="1" fill="none"/>
                  <path d="M8 14h8M8 18h6" stroke="#0078d4" stroke-width="1.4" stroke-linecap="round"/>
                </svg>
              </span>
              <span class="name-stack">
                <span class="name-text">{{ row.name }}</span>
                <span v-if="row.modulePath" class="name-module-hint muted">{{ row.modulePath }}</span>
              </span>
            </span>
            <span class="col-date muted">{{ row.dateLabel }}</span>
            <span class="col-type muted">{{ row.typeLabel }}</span>
            <span
              class="col-size muted col-size-num"
              :title="row.sizeTitle"
            >{{ row.sizeLabel }}</span>
          </button>
        </li>
      </ul>
      <p v-if="rows.length === 0 && !folderSearchQuery.trim()" class="empty-folder">This folder is empty.</p>
      <p v-else-if="folderSearchQuery.trim() && folderSearchLoading" class="empty-folder">Searching…</p>
      <p
        v-else-if="folderSearchQuery.trim() && !folderSearchLoading && displayRows.length === 0"
        class="empty-folder"
      >No Lean files match your search under this folder.</p>
    </div>
  </div>
</template>

<script setup>
import Vue from '../js/vue.js';
import searchForm from './searchForm.vue';

const props = defineProps({
  packages: { type: Array, default: () => [] },
  theorems: { type: Array, default: () => [] },
});

const self = new Vue({
  components: { searchForm },
  props,

  $refs: {
    explorerRoot: null,
    folderSearchInputRef: null,
  },

  data: {
    issearch: false,
    q: '',
    caseSensitive: false,
    wholeWord: false,
    regularExpression: false,
    nlp: false,
    fullText: false,
    folderSearchOpen: false,
    folderSearchQuery: '',
    folderSearchInputId: 'explorer-folder-search-q',
    folderSearchHits: /** @type {null | object[]} */ (null),
    folderSearchLoading: false,
    selectedIndex: 0,
  },

  computed: {
    rows() {
      const folders = (this.packages || []).map((raw) => {
        const e = normalizeListingEntry(raw);
        return {
          name: e.name,
          kind: /** @type {const} */ ('folder'),
          typeLabel: 'File folder',
          dateLabel: formatExplorerDate(e.mtimeMs),
          sizeLabel: formatExplorerSize(e.size),
          sizeTitle: 'File folder',
        };
      });
      const files = (this.theorems || []).map((raw) => {
        const e = normalizeListingEntry(raw);
        const hasBytes = typeof e.size === 'number' && Number.isFinite(e.size);
        return {
          name: e.name,
          kind: /** @type {const} */ ('lean'),
          typeLabel: 'Lean source file',
          dateLabel: formatExplorerDate(e.mtimeMs),
          sizeLabel: formatExplorerSize(e.size),
          sizeTitle: hasBytes ? `${e.size} bytes` : 'Size not available',
        };
      });
      folders.sort((a, b) => a.name.localeCompare(b.name, undefined, { sensitivity: 'base' }));
      files.sort((a, b) => a.name.localeCompare(b.name, undefined, { sensitivity: 'base' }));
      return [...folders, ...files];
    },

    moduleParam() {
      const raw = typeof getParameterByName === 'function' ? getParameterByName('module') : null;
      return raw ? String(raw) : '';
    },

    breadcrumbParts() {
      const m = this.moduleParam.replace(/\/+$/, '');
      if (!m) return [];
      return m.split(/[./]/).filter(Boolean);
    },

    currentFolderLabel() {
      const p = this.breadcrumbParts;
      if (p.length) return p[p.length - 1];
      return 'Lemma';
    },

    displayRows() {
      const needle = this.folderSearchQuery.trim();
      if (!needle) return this.rows;
      if (this.folderSearchLoading && this.folderSearchHits === null) return [];
      return this.folderSearchHits ?? [];
    },

    activeId() {
      return this.displayRows.length ? `explorer-row-${this.selectedIndex}` : undefined;
    },
  },

  watch: {
    displayRows(list) {
      if (list.length === 0) this.selectedIndex = 0;
      else if (this.selectedIndex >= list.length) this.selectedIndex = list.length - 1;
    },
    folderSearchQuery() {
      if (folderSearchTimer) {
        clearTimeout(folderSearchTimer);
        folderSearchTimer = null;
      }
      const raw = this.folderSearchQuery.trim();
      if (!raw) {
        this.folderSearchHits = null;
        this.folderSearchLoading = false;
        return;
      }
      this.folderSearchLoading = true;
      this.folderSearchHits = null;
      folderSearchTimer = setTimeout(async () => {
        folderSearchTimer = null;
        const qStable = this.folderSearchQuery.trim();
        if (!qStable) {
          this.folderSearchLoading = false;
          return;
        }
        const seq = ++folderSearchSeq;
        try {
          const seg = typeof axiom_user === 'function' ? axiom_user() : 'lean';
          const folder = this.moduleParam.replace(/\//g, '.').replace(/\.+$/, '');
          const url = new URL(`/${seg}/api/folder-search.json`, location.origin);
          url.searchParams.set('folder', folder);
          url.searchParams.set('q', qStable);
          const res = await fetch(url.toString(), { credentials: 'same-origin' });
          if (!res.ok) throw new Error(String(res.status));
          const data = await res.json();
          if (seq !== folderSearchSeq) return;
          this.folderSearchHits = (data.hits || []).map((h) => ({
            kind: /** @type {const} */ ('lean'),
            name: h.name,
            leanModule: h.module,
            modulePath: h.module,
            typeLabel: 'Lean source file',
            dateLabel: formatExplorerDate(h.mtimeMs),
            sizeLabel: formatExplorerSize(h.size),
            sizeTitle: `${h.size} bytes`,
          }));
        } catch (e) {
          console.error(e);
          if (seq === folderSearchSeq) this.folderSearchHits = [];
        } finally {
          if (seq === folderSearchSeq) this.folderSearchLoading = false;
        }
      }, 250);
    },
  },

  mounted() {
    this.$nextTick(() => {
      this.explorerRoot?.focus?.();
    });
    const hit = this.focusRowFromHash();
    if (!hit && this.displayRows.length) {
      this.$nextTick(() => {
        this.explorerRoot?.querySelector?.('.row-inner')?.focus?.();
      });
    }
    if (this.rows.length === 0 && this.packages.length === 0 && this.theorems.length === 0) {
      this.issearch = true;
      const mod = this.moduleParam;
      if (mod) this.q = mod.split(/[./]/).slice(1).join('.');
    }
  },

  unmounted() {
    if (folderSearchTimer) clearTimeout(folderSearchTimer);
  },

  methods: {
    crumbHref(index) {
      const parts = this.breadcrumbParts.slice(0, index + 1);
      const mod = parts.join('/');
      const q = new URLSearchParams();
      q.set('module', mod);
      return `${location.pathname}?${q.toString()}`;
    },
    selectRow(idx) {
      if (idx >= 0 && idx < this.displayRows.length) this.selectedIndex = idx;
    },
    openFolderSearch() {
      this.folderSearchOpen = true;
      this.$nextTick(() => {
        const el = this.folderSearchInputRef;
        el?.focus();
        el?.select();
      });
    },
    closeFolderSearch() {
      this.folderSearchOpen = false;
      this.folderSearchQuery = '';
      this.folderSearchHits = null;
      this.folderSearchLoading = false;
      folderSearchSeq += 1;
      if (folderSearchTimer) {
        clearTimeout(folderSearchTimer);
        folderSearchTimer = null;
      }
      this.$nextTick(() => this.explorerRoot?.focus());
    },
    async deleteSelectedLeanFile() {
      const row = this.displayRows[this.selectedIndex];
      if (!row || row.kind !== 'lean') return;

      const pl = packageAndLemmaForDeleteRow(row);
      if (!pl) return;

      if (!confirm(`Delete lemma file “${row.name}”?`)) return;

      try {
        await form_post('php/request/delete/lemma.php', {
          package: pl.package,
          lemma: pl.lemma,
        });
        location.reload();
      } catch (e) {
        console.error(e);
        alert(`Delete failed: ${e && e.message ? e.message : String(e)}`);
      }
    },
    async deleteSelectedFolder() {
      const row = this.displayRows[this.selectedIndex];
      if (!row || row.kind !== 'folder') return;

      const pkg = packageFromModuleQuery();
      if (!pkg) return;

      if (!confirm(`Delete folder “${row.name}” and everything inside it?`)) return;

      try {
        await form_post('php/request/delete/package.php', {
          package: pkg,
          section: row.name,
        });
        location.reload();
      } catch (e) {
        console.error(e);
        alert(`Delete failed: ${e && e.message ? e.message : String(e)}`);
      }
    },
    /** Keep the active row visible inside `.item-list`; focus stays on `.explorer`, so arrows/Home/End do not scroll by default. */
    scrollSelectedRowIntoView() {
      this.$nextTick(() => {
        const el = document.getElementById(`explorer-row-${this.selectedIndex}`);
        el?.scrollIntoView({ block: 'nearest' });
      });
    },
    onExplorerKeydown(event) {
      if (this.issearch) return;
      const key = event.key;

      if ((key === 'f' || key === 'F') && event.ctrlKey) {
        event.preventDefault();
        if (event.shiftKey) {
          this.issearch = true;
          return;
        }
        this.openFolderSearch();
        return;
      }

      if (key === 'Escape' && this.folderSearchOpen) {
        event.preventDefault();
        this.closeFolderSearch();
        return;
      }

      if (this.folderSearchOpen && isEventFromFolderSearchInput(event)) {
        if (['ArrowDown', 'ArrowUp', 'Enter', 'Home', 'End', 'Delete'].includes(key)) {
          return;
        }
      }

      if (this.displayRows.length === 0) return;

      if (key === 'ArrowDown') {
        this.selectedIndex = Math.min(this.selectedIndex + 1, this.displayRows.length - 1);
        event.preventDefault();
        this.scrollSelectedRowIntoView();
      } else if (key === 'ArrowUp') {
        this.selectedIndex = Math.max(this.selectedIndex - 1, 0);
        event.preventDefault();
        this.scrollSelectedRowIntoView();
      } else if (key === 'Enter') {
        const row = this.displayRows[this.selectedIndex];
        if (row) openRow(row);
        event.preventDefault();
      } else if (key === 'Home') {
        this.selectedIndex = 0;
        event.preventDefault();
        this.scrollSelectedRowIntoView();
      } else if (key === 'End') {
        this.selectedIndex = this.displayRows.length - 1;
        event.preventDefault();
        this.scrollSelectedRowIntoView();
      } else if (key === 'Delete') {
        const row = this.displayRows[this.selectedIndex];
        if (row?.kind === 'lean') {
          event.preventDefault();
          this.deleteSelectedLeanFile();
        } else if (row?.kind === 'folder') {
          event.preventDefault();
          this.deleteSelectedFolder();
        }
      }
    },
    focusRowFromHash() {
      const hash = location.hash ? location.hash.slice(1) : '';
      if (!hash) return false;
      const i = this.displayRows.findIndex((r) => r.name === hash);
      if (i < 0) return false;
      this.selectedIndex = i;
      this.$nextTick(() => {
        const el = document.getElementById(`explorer-row-${i}`);
        el?.scrollIntoView({ block: 'nearest' });
        el?.querySelector('.row-inner')?.focus?.();
      });
      return true;
    },
  },
});

const {
  $refs,
  issearch,
  q,
  caseSensitive,
  wholeWord,
  regularExpression,
  nlp,
  fullText,
  folderSearchOpen,
  folderSearchQuery,
  folderSearchInputId,
  folderSearchLoading,
  selectedIndex,
  rows,
  breadcrumbParts,
  currentFolderLabel,
  displayRows,
  activeId,
  crumbHref,
  selectRow,
  openFolderSearch,
  closeFolderSearch,
  onExplorerKeydown,
} = self.globals;

/** Match `?module=` URL rules (slash vs dotted path segments). */
function appendModuleSegment(segment, asFolder) {
  const u = new URL(location.href);
  const haystack = u.search;
  let mod = u.searchParams.get('module') || '';
  const usesDots = haystack.indexOf('.') >= 0;

  if (usesDots) {
    mod = mod.replace(/\.+$/, '');
    if (mod.length === 0) mod = segment;
    else if (mod.endsWith('.')) mod += segment;
    else mod = `${mod}.${segment}`;
    if (asFolder) mod += '.';
  } else {
    mod = mod.replace(/\/+$/, '');
    if (mod.length === 0) mod = asFolder ? `${segment}/` : segment;
    else mod = asFolder ? `${mod}/${segment}/` : `${mod}/${segment}`;
  }

  u.searchParams.set('module', mod);
  return `${u.origin}${u.pathname}${u.search}${location.hash}`;
}

function openRow(row) {
  if (row.leanModule) {
    const u = new URL(location.href);
    u.searchParams.set('module', row.leanModule);
    location.href = u.toString();
    return;
  }
  location.href = appendModuleSegment(row.name, row.kind === 'folder');
}

function isEventFromFolderSearchInput(event) {
  const t = event.target;
  return t instanceof HTMLElement && !!t.closest('.folder-search-panel');
}

/**
 * Same contract as `php/request/delete/lemma.php`:
 * `package` = dotted path from `?module=` (strip trailing `.`), `lemma` = basename without `.lean`.
 */
/** Parent dotted module for `php/request/delete/*.php` (strip trailing `.` from `?module=`). */
function packageFromModuleQuery() {
  const u = new URL(location.href);
  let pkg = (u.searchParams.get('module') || '').replace(/\//g, '.').trim();
  if (!pkg) return '';
  return pkg.replace(/\.+$/, '');
}

/** For delete-lemma POST: parent package + leaf name (handles recursive-search rows). */
function packageAndLemmaForDeleteRow(row) {
  if (row.leanModule) {
    const full = row.leanModule;
    const i = full.lastIndexOf('.');
    if (i <= 0) return null;
    return { package: full.slice(0, i), lemma: full.slice(i + 1) };
  }
  const pkg = packageFromModuleQuery();
  if (!pkg) return null;
  return { package: pkg, lemma: row.name };
}

/** Listing column helpers (used by `rows` / folder-search mapping). */
/** @param {unknown} v */
function toFiniteNumber(v) {
  if (typeof v === 'number' && Number.isFinite(v)) return v;
  if (typeof v === 'string' && v.trim() !== '') {
    const n = Number(v);
    if (Number.isFinite(n)) return n;
  }
  return null;
}

/** @param {unknown} raw @returns {{ name: string, mtimeMs: number | null, size: number | null }} */
function normalizeListingEntry(raw) {
  if (raw != null && typeof raw === 'object' && 'name' in raw) {
    const o = /** @type {{ name: unknown, mtimeMs?: unknown, size?: unknown }} */ (raw);
    const mtimeMs = toFiniteNumber(o.mtimeMs);
    let size = null;
    if (o.size !== undefined && o.size !== null && o.size !== '') {
      size = toFiniteNumber(o.size);
    }
    return { name: String(o.name), mtimeMs, size };
  }
  return { name: String(raw), mtimeMs: null, size: null };
}

/** Windows-style size column (bytes → KB / MB / GB). Folders → em dash. */
function formatExplorerSize(bytes) {
  if (bytes == null) return '—';
  if (bytes < 1024) return `${bytes} B`;
  const kb = bytes / 1024;
  if (kb < 1024) {
    const s = kb >= 100 ? kb.toFixed(0) : kb >= 10 ? kb.toFixed(1) : kb.toFixed(2);
    return `${s} KB`;
  }
  const mb = kb / 1024;
  if (mb < 1024) {
    const s = mb >= 100 ? mb.toFixed(0) : mb >= 10 ? mb.toFixed(1) : mb.toFixed(2);
    return `${s} MB`;
  }
  const gb = mb / 1024;
  const s = gb >= 100 ? gb.toFixed(0) : gb >= 10 ? gb.toFixed(1) : gb.toFixed(2);
  return `${s} GB`;
}

function formatExplorerDate(mtimeMs) {
  if (mtimeMs == null || !Number.isFinite(mtimeMs)) return '—';
  try {
    return new Date(mtimeMs).toLocaleString(undefined, {
      year: 'numeric',
      month: 'numeric',
      day: 'numeric',
      hour: 'numeric',
      minute: '2-digit',
    });
  } catch {
    return '—';
  }
}

/** Folder-search debounce (module scope; single explorer mount). */
let folderSearchTimer = /** @type {ReturnType<typeof setTimeout> | null} */ (null);
let folderSearchSeq = 0;
</script>

<style scoped>
.explorer {
  margin: 0;
  padding: 0;
  font-family: 'Segoe UI Variable', 'Segoe UI', system-ui, -apple-system, sans-serif;
  font-size: 13px;
  color: #1a1a1a;
  outline: none;
  min-height: 100vh;
  box-sizing: border-box;
  display: flex;
  flex-direction: column;
}

.explorer-toolbar {
  flex-shrink: 0;
  padding: 10px 12px 8px;
  background: linear-gradient(180deg, #f9f9f9 0%, #f3f3f3 100%);
  border: 1px solid #e0e0e0;
  border-bottom: none;
  border-radius: 8px 8px 0 0;
}

.explorer-toolbar-row {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  justify-content: space-between;
  gap: 10px 16px;
}

.toolbar-search-area {
  flex: 0 0 auto;
  margin-left: auto;
  display: flex;
  align-items: center;
  min-height: 32px;
}

.toolbar-search-fab {
  display: flex;
  align-items: center;
  justify-content: center;
  width: 36px;
  height: 32px;
  padding: 0;
  border: 1px solid #c4c4c4;
  border-radius: 4px;
  background: #fff;
  color: #323130;
  cursor: pointer;
  box-shadow: 0 1px 2px rgba(0, 0, 0, 0.06);
}

.toolbar-search-fab:hover {
  background: #f5f5f5;
  border-color: #a19f9d;
}

.toolbar-search-icon {
  width: 18px;
  height: 18px;
}

.folder-search-panel {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 8px 10px;
  min-width: min(100%, 320px);
  max-width: min(100%, 420px);
  padding: 6px 10px;
  border: 1px solid #c4c4c4;
  border-radius: 6px;
  background: #ffffff;
  box-shadow: 0 1px 3px rgba(0, 0, 0, 0.08);
}

.folder-search-label {
  flex: 1 1 100%;
  font-size: 12px;
  font-weight: 600;
  color: #323130;
  margin: 0;
  line-height: 1.2;
}

.folder-search-input {
  flex: 1 1 160px;
  min-width: 0;
  height: 28px;
  padding: 0 8px;
  border: 1px solid #8a8886;
  border-radius: 4px;
  font: inherit;
  font-size: 13px;
  box-sizing: border-box;
}

.folder-search-input:focus {
  outline: 2px solid #0067c0;
  outline-offset: 1px;
  border-color: #0067c0;
}

.folder-search-close {
  flex: 0 0 auto;
  width: 28px;
  height: 28px;
  padding: 0;
  border: none;
  border-radius: 4px;
  background: transparent;
  color: #605e5c;
  font-size: 20px;
  line-height: 1;
  cursor: pointer;
}

.folder-search-close:hover {
  background: rgba(0, 0, 0, 0.06);
  color: #323130;
}

.breadcrumb {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 4px;
  font-size: 13px;
}

.crumb,
.crumb.root {
  color: #0067c0;
  text-decoration: none;
}

.crumb:hover,
.crumb.root:hover {
  text-decoration: underline;
}

.crumb-sep {
  color: #8a8a8a;
  user-select: none;
  font-size: 12px;
}

.explorer-frame {
  flex: 1 1 auto;
  min-height: 0;
  display: flex;
  flex-direction: column;
  background: #ffffff;
  border: 1px solid #e0e0e0;
  border-radius: 0 0 8px 8px;
  box-shadow: 0 1px 2px rgba(0, 0, 0, 0.06);
  overflow: hidden;
}

.col-header {
  flex-shrink: 0;
  display: grid;
  grid-template-columns: minmax(0, 1fr) 12.5rem 11rem 5.75rem;
  gap: 8px;
  padding: 6px 12px;
  background: #fafafa;
  border-bottom: 1px solid #e5e5e5;
  font-size: 12px;
  font-weight: 600;
  color: #5c5c5c;
}

.col-size {
  text-align: right;
}

.col-header .col-size {
  padding-right: 2px;
}

.item-list {
  list-style: none;
  margin: 0;
  padding: 4px 0;
  flex: 1 1 auto;
  min-height: 0;
  overflow: auto;
}

.item-row {
  margin: 0;
  padding: 0;
}

.item-row.selected {
  background: rgba(0, 120, 212, 0.12);
}

.row-inner {
  display: grid;
  grid-template-columns: minmax(0, 1fr) 12.5rem 11rem 5.75rem;
  gap: 8px;
  align-items: center;
  width: 100%;
  padding: 4px 12px;
  border: none;
  background: transparent;
  font: inherit;
  text-align: left;
  cursor: pointer;
  color: inherit;
}

.col-size-num {
  text-align: right;
  font-variant-numeric: tabular-nums;
  padding-right: 2px;
}

.item-row:hover .row-inner {
  background: rgba(0, 0, 0, 0.04);
}

.item-row.selected .row-inner {
  background: transparent;
}

.cell-name {
  display: flex;
  align-items: center;
  gap: 10px;
  min-width: 0;
}

.file-icon {
  flex-shrink: 0;
  width: 20px;
  height: 20px;
  display: flex;
  align-items: center;
  justify-content: center;
}

.ico-svg {
  width: 20px;
  height: auto;
  display: block;
}

.ico-lean {
  width: 18px;
}

.name-stack {
  display: flex;
  flex-direction: column;
  align-items: flex-start;
  min-width: 0;
  gap: 2px;
}

.name-text {
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
  max-width: 100%;
}

.name-module-hint {
  font-size: 11px;
  line-height: 1.2;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
  max-width: 100%;
}

.muted {
  color: #767676;
  font-size: 12px;
}

.empty-folder {
  padding: 24px 16px;
  color: #767676;
  text-align: center;
}
</style>