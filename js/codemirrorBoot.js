// CodeMirror 6 boot: creates and configures editor instances.
// Replaces the old CM5 dynamic-import chain with proper ESM imports.

import { EditorState, EditorSelection, StateEffect, Transaction, Prec } from "@codemirror/state";
import { EditorView, keymap, lineNumbers, highlightActiveLine, drawSelection, highlightSpecialChars, rectangularSelection, crosshairCursor } from "@codemirror/view";
import { defaultKeymap, history, historyKeymap, indentMore } from "@codemirror/commands";
import { bracketMatching, foldGutter, indentOnInput, StreamLanguage, HighlightStyle, syntaxHighlighting, defaultHighlightStyle } from "@codemirror/language";
import { tags as t } from "@lezer/highlight";
import { autocompletion, completionKeymap, startCompletion } from "@codemirror/autocomplete";
import { searchKeymap, highlightSelectionMatches } from "@codemirror/search";
import { leanMode, leanHintWords } from "./codemirror-lean.js";
import { CMBridge, CodeMirror, deleteToLineEnd } from "./codemirror.js";

// Eclipse-like theme for CM6
const eclipseTheme = EditorView.theme({
  "&": {
    backgroundColor: "rgb(199, 237, 204)",
    color: "#000",
    fontSize: "1em",
    fontFamily: "Consolas, monospace",
    height: "auto",
  },
  ".cm-scroller": {
    fontFamily: "Consolas, monospace",
  },
  ".cm-content": {
    fontFamily: "Consolas, monospace",
  },
  // Semi-transparent: selection layer sits behind content, so an opaque
  // active-line white hid the selection on the current line.
  ".cm-activeLine": { backgroundColor: "rgba(255,255,255,0.45)" },
  ".cm-activeLineGutter": { backgroundColor: "rgba(255,255,255,0.45)" },
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
    highlightActiveLine(),
    highlightSelectionMatches(),
    bracketMatching(),
    indentOnInput(),
    leanLanguage,
    syntaxHighlighting(eclipseHighlightStyle),
    syntaxHighlighting(defaultHighlightStyle, { fallback: true }),
    eclipseTheme,
    EditorView.lineWrapping,
    EditorState.allowMultipleSelections.of(true),
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
    ...searchKeymap,
  ]));

  // Autocomplete
  if (options.hintFn) {
    additionalExts.push(autocompletion({
      override: [{
        async provideCompletions(context) {
          if (!context.explicit && !context.matchBefore(/[\w.\\]+/))
            return null;
          const result = await options.hintFn(bridge);
          if (!result || !result.list) return null;
          const doc = context.state.doc;
          const from = result.from ? posToOffset(doc, result.from.line, result.from.ch) : context.pos;
          const to = result.to ? posToOffset(doc, result.to.line, result.to.ch) : context.pos;
          return {
            from,
            to,
            options: result.list.map(item => ({
              label: typeof item === 'string' ? item : item.text,
              type: 'keyword',
            })),
          };
        }
      }],
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

