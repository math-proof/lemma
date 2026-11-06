// CodeMirror 6 boot: creates and configures editor instances.
// Replaces the old CM5 dynamic-import chain with proper ESM imports.

import { EditorState, EditorSelection, StateEffect, Transaction, Prec } from "@codemirror/state";
import { EditorView, keymap, lineNumbers, drawSelection, highlightSpecialChars, rectangularSelection, crosshairCursor, panels, Decoration, WidgetType, MatchDecorator, ViewPlugin } from "@codemirror/view";
import { defaultKeymap, history, historyKeymap, indentMore } from "@codemirror/commands";
import { bracketMatching, foldGutter, indentOnInput, StreamLanguage, HighlightStyle, syntaxHighlighting, defaultHighlightStyle } from "@codemirror/language";
import { tags as t } from "@lezer/highlight";
import { autocompletion, completionKeymap, startCompletion } from "@codemirror/autocomplete";
import {
  search,
  highlightSelectionMatches,
  openSearchPanel,
  closeSearchPanel,
  searchPanelOpen,
  findNext,
  findPrevious,
  selectSelectionMatches,
  selectNextOccurrence,
  gotoLine,
} from "@codemirror/search";
import { leanMode, leanHintWords } from "./codemirror-lean.js";
import { CMBridge, CodeMirror, deleteToLineEnd, cmMarkField } from "./codemirror.js";

// Eclipse-like theme for CM6
const eclipseTheme = EditorView.theme({
  "&": {
    backgroundColor: "rgb(199, 237, 204)",
    color: "#000",
    fontSize: "1em",
    fontFamily: "Consolas, monospace",
    height: "auto",
  },
  // Inset focus ring: the default outward outline collides with `.bottom-line`
  // dates (`Created on …`) that sit immediately under the last editor.
  "&.cm-focused": {
    outline: "1px dotted #212121",
    outlineOffset: "-1px",
  },
  ".cm-scroller": {
    fontFamily: "Consolas, monospace",
  },
  ".cm-content": {
    fontFamily: "Consolas, monospace",
  },
  // No highlightActiveLine(): CM always has a selection head (even unfocused),
  // so every editor’s first line would get .cm-activeLine and look white on mint.
  ".cm-cursor": {
    borderLeft: "2px solid red",
  },
  ".cm-gutters": {
    backgroundColor: "rgb(199, 237, 204)",
    border: "none",
  },
  ".cm-tooltip-autocomplete": {
    boxSizing: "border-box",
  },
  // Opaque selection. CM6 base theme uses
  // `&.cm-focused .cm-scroller .cm-selectionBackground` with translucent
  // fills that vanish on the green eclipse bg — match that specificity.
  ".cm-scroller .cm-selectionBackground": {
    backgroundColor: "#b4d7ff !important",
  },
  "&.cm-focused .cm-scroller .cm-selectionBackground": {
    backgroundColor: "#a0c8ff !important",
  },
  // Native fallback if drawSelection layer is skipped
  ".cm-content ::selection": {
    backgroundColor: "#a0c8ff",
  },
  ".cm-guillemet-katex": {
    display: "inline-block",
    verticalAlign: "middle",
    lineHeight: "1",
  },
  ".cm-guillemet-katex .katex": {
    fontSize: "1em",
  },
}, { dark: false });

// Syntax highlighting style (eclipse-like colors).
// No `class` props: with a static `class` CM6 skips emitting the color
// rules, so let HighlightStyle generate and mount its own stylesheet.
const eclipseHighlightStyle = HighlightStyle.define([
  { tag: t.keyword, color: "#7f0055", fontWeight: "bold" },
  { tag: t.atom, color: "#7f0055" },
  { tag: t.number, color: "#0000ff" },
  { tag: t.definition(t.variableName), color: "#0000ff" },
  { tag: t.standard(t.variableName), color: "#7f0055" },
  { tag: t.special(t.variableName), color: "#000" },
  { tag: t.string, color: "#2a00ff" },
  { tag: t.comment, color: "#3f7f5f", fontStyle: "italic" },
  { tag: t.variableName, color: "#000" },
  { tag: t.function(t.variableName), color: "#000" },
  { tag: t.propertyName, color: "#644" },
  { tag: t.punctuation, color: "#000" },
  { tag: t.operator, color: "#000" },
  { tag: t.meta, color: "#555" },
  { tag: t.bracket, color: "#000" },
]);

const leanLanguage = StreamLanguage.define(leanMode);


/** «latex…» Lean identifiers → inline KaTeX (musical notes, \sf{w}, …). */
class GuillemetKatexWidget extends WidgetType {
  constructor(inner) {
    super();
    this.inner = inner;
  }
  eq(other) {
    return other instanceof GuillemetKatexWidget && other.inner === this.inner;
  }
  toDOM() {
    const wrap = document.createElement("span");
    wrap.className = "cm-guillemet-katex";
    wrap.title = "«" + this.inner + "»";
    const katexApi = typeof katex !== "undefined" ? katex : (typeof window !== "undefined" ? window.katex : null);
    if (!katexApi) {
      wrap.textContent = "«" + this.inner + "»";
      return wrap;
    }
    try {
      // Same sanitization idea as js/utility.js (✝ → \dagger).
      const latex = String(this.inner).replace(/‡/g, "\\ddagger").replace(/[†✝]/gi, "\\dagger");
      katexApi.render(latex, wrap, { throwOnError: false, displayMode: false, errorColor: "#ff0000" });
    } catch (e) {
      wrap.textContent = "«" + this.inner + "»";
    }
    return wrap;
  }
  ignoreEvent() {
    return false;
  }
}

const guillemetKatexMatcher = new MatchDecorator({
  regexp: /«([^»\n]*)»/g,
  decoration: (match, view, pos) => {
    // While the caret/selection overlaps this guillemet, show raw Lean source for editing.
    const end = pos + match[0].length;
    for (const r of view.state.selection.ranges) {
      if (r.from < end && r.to > pos) return null;
    }
    const inner = match[1];
    return Decoration.replace({
      widget: new GuillemetKatexWidget(inner),
    });
  },
  boundary: /[^«»]/,
});

const guillemetKatex = ViewPlugin.fromClass(
  class {
    constructor(view) {
      this.decorations = guillemetKatexMatcher.createDeco(view);
    }
    update(update) {
      this.decorations = guillemetKatexMatcher.updateDeco(update, this.decorations);
    }
  },
  { decorations: (v) => v.decorations }
);



// One page-level Find/Replace: every EditorView shares a sticky host, and
// Mod-f closes any other open CM search panel before opening on the focused view.
const liveEditorViews = new Set();

function getGlobalSearchHost() {
  let host = document.getElementById("cm-global-search-host");
  if (!host) {
    host = document.createElement("div");
    host.id = "cm-global-search-host";
    Object.assign(host.style, {
      position: "sticky",
      top: "0",
      zIndex: "10000",
      background: "rgb(199, 237, 204)",
    });
    document.body.insertBefore(host, document.body.firstChild);
  }
  return host;
}

function pruneDisconnectedViews() {
  for (const v of [...liveEditorViews]) {
    if (!v.dom.isConnected)
      liveEditorViews.delete(v);
  }
}

function openPageSearchPanel(view) {
  pruneDisconnectedViews();
  for (const other of liveEditorViews) {
    if (other !== view && searchPanelOpen(other.state))
      closeSearchPanel(other);
  }
  return openSearchPanel(view);
}

/** Same chords as @codemirror/search searchKeymap, but Mod-f is exclusive. */
const pageSearchKeymap = [
  { key: "Mod-f", run: openPageSearchPanel, scope: "editor search-panel" },
  { key: "F3", run: findNext, shift: findPrevious, scope: "editor search-panel", preventDefault: true },
  { key: "Mod-g", run: findNext, shift: findPrevious, scope: "editor search-panel", preventDefault: true },
  { key: "Escape", run: closeSearchPanel, scope: "editor search-panel" },
  { key: "Mod-Shift-l", run: selectSelectionMatches },
  { key: "Mod-Alt-g", run: gotoLine },
  { key: "Mod-d", run: selectNextOccurrence, preventDefault: true },
];


/**
 * Create a CodeMirror 6 editor instance wrapped in a CM5-compatible bridge.
 * @param {HTMLElement} parent - The element to mount the editor into
 * @param {Object} options - { doc, lineNumbers, styleActiveLine, extraKeys, hintFn }
 * @returns {CMBridge}
 */
export function createEditor(parent, options = {}) {
  // CM5 fromTextArea: wrap/hide a <textarea>; CM6 EditorView needs a non-textarea parent.
  let mount = parent;
  let textarea = null;
  if (parent && parent.nodeName === "TEXTAREA") {
    textarea = parent;
    mount = document.createElement("div");
    mount.className = "cm-textarea-host";
    if (textarea.nextSibling)
      textarea.parentNode.insertBefore(mount, textarea.nextSibling);
    else
      textarea.parentNode.appendChild(mount);
    textarea.style.display = "none";
    if (!options.doc && textarea.value)
      options = { ...options, doc: textarea.value };
  }

  const extensions = [
    history(),
    drawSelection(),
    highlightSpecialChars(),
    highlightSelectionMatches(),
    bracketMatching(),
    indentOnInput(),
    leanLanguage,
    syntaxHighlighting(eclipseHighlightStyle),
    syntaxHighlighting(defaultHighlightStyle, { fallback: true }),
    eclipseTheme,
    EditorView.lineWrapping,
    EditorState.allowMultipleSelections.of(true),
    cmMarkField, // CM5 markText / erroneous-text underlines (render.vue focus)
    guillemetKatex, // «λ_{…}» / «\\sf{w}» → inline KaTeX
    // Shared sticky host + search({ top }) so Find/Replace is page-level, not per-box.
    panels({ topContainer: getGlobalSearchHost() }),
    search({ top: true }),
  ];

  if (options.lineNumbers === true)
    extensions.push(lineNumbers());

  // Keep a backing <textarea> in sync (form submit / Vue bindings), like CM5 fromTextArea.
  if (textarea) {
    extensions.push(EditorView.updateListener.of((update) => {
      if (update.docChanged)
        textarea.value = update.state.doc.toString();
    }));
  }

  // Build the view first (without keybindings/autocomplete)
  const state = EditorState.create({
    doc: options.doc || "",
    extensions: [...extensions],
  });

  const view = new EditorView({ state, parent: mount });
  liveEditorViews.add(view);
  const _destroyView = view.destroy.bind(view);
  view.destroy = () => {
    liveEditorViews.delete(view);
    _destroyView();
  };
  const bridge = new CMBridge(view);
  if (textarea) {
    bridge.textarea = textarea;
    // Initial sync in case options.doc differed from the live value
    textarea.value = view.state.doc.toString();
  }

  // Now add keybindings and autocomplete as additional extensions
  const additionalExts = [];

  // Custom keybindings first (Prec.high) so they override CM6 defaults.
  // CM5 used "Ctrl-Home"; CM6 defaults bind "Mod-Home" (Ctrl on Win/Linux)
  // to cursorDocStart/End — alias Ctrl-* → Mod-* for those chords.
  const keyMap = {
    'Left': 'ArrowLeft',
    'Right': 'ArrowRight',
    'Up': 'ArrowUp',
    'Down': 'ArrowDown',
  };
  const customBindings = [];
  if (options.extraKeys) {
    for (const [key, handler] of Object.entries(options.extraKeys)) {
      let cm6Key = keyMap[key] || key;
      const keys = new Set([cm6Key]);
      if (cm6Key.startsWith('Ctrl-'))
        keys.add('Mod-' + cm6Key.slice('Ctrl-'.length));
      for (const k of keys) {
        customBindings.push({
          key: k,
          run: () => { handler(bridge); return true; },
          preventDefault: true,
        });
      }
    }
  }
  if (customBindings.length)
    additionalExts.push(Prec.high(keymap.of(customBindings)));

  additionalExts.push(keymap.of([
    ...defaultKeymap,
    ...historyKeymap,
    ...completionKeymap,
    ...pageSearchKeymap,
  ]));

  // Autocomplete — `override` must be `CompletionSource` functions
  // (`(context) => …`). An object here makes CM6 call `active.source(…)`
  // on blur and throw `TypeError: active.source is not a function`
  // (breaks Space after `\sqcup` / `\sqrt` Unicode hints).
  if (options.hintFn) {
    additionalExts.push(autocompletion({
      override: [
        async (context) => {
          // Require a real abbr/word — bare `\\` alone used to call hintFn and
          // crash on match()[0] (blur/startQuery + activateOnTyping race).
          if (!context.explicit && !context.matchBefore(/[\w.]+|\\[\w.|<>=^~{} \\+\p{Script=Greek}-]+/u))
            return null;
          // Do not name a local `options` — it shadows createEditor's `options`
          // and TDZ-crashes on `options.hintFn` (`Cannot access 'options' before initialization`).
          let result;
          try {
            result = await options.hintFn(bridge);
          } catch (err) {
            console.warn('hintFn failed', err);
            return null;
          }
          if (!result || !result.list?.length) return null;
          const doc = context.state.doc;
          const from = result.from ? posToOffset(doc, result.from.line, result.from.ch) : context.pos;
          const to = result.to ? posToOffset(doc, result.to.line, result.to.ch) : context.pos;
          const completions = result.list.map(item => ({
            label: typeof item === 'string' ? item : item.text,
            type: 'keyword',
          }));
          // CM5 `completeSingle`: one hit (e.g. `\sqcup` → `⊔`) inserts immediately.
          if (completions.length === 1) {
            const insert = completions[0].label;
            context.view.dispatch({
              changes: { from, to, insert },
              selection: { anchor: from + insert.length },
              userEvent: 'input.complete',
            });
            return null;
          }
          // Labels are replacements (unicode / other latex), not prefixes of the
          // typed text — CM6's default filter would drop `⊔` for `\sqcup`.
          return { from, to, filter: false, options: completions };
        },
      ],
    }));
  }

  // Add the additional extensions to the existing view
  view.dispatch({
    effects: additionalExts.map(ext => StateEffect.appendConfig.of(ext)),
  });

  return bridge;
}

function posToOffset(doc, line, ch) {
  const l = doc.line(Math.max(1, Math.min(doc.lines, line + 1)));
  return Math.max(l.from, Math.min(l.to, l.from + ch));
}

// Preload function for backward compatibility
let _ready = null;
export function preloadCodeMirror() {
  if (!_ready) {
    _ready = Promise.resolve(true);
  }
  return _ready;
}

// Re-export for convenience
export { CodeMirror, CMBridge, deleteToLineEnd };

// Auto-preload
preloadCodeMirror();

// Expose to window for SFC-loaded scripts that can't use bare ESM imports
window.cmBoot = { createEditor, CodeMirror, CMBridge, deleteToLineEnd, preloadCodeMirror };

