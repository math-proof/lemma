// CM5-compatible bridge around CM6 EditorView.
// Provides getCursor/getLine/setCursor/replaceSelection/etc. so that
// existing keybinding handlers and hint logic need minimal changes.

import { EditorView, Decoration } from "@codemirror/view";
import { EditorSelection, StateEffect, StateField } from "@codemirror/state";
import { startCompletion } from "@codemirror/autocomplete";
import { toggleComment } from "@codemirror/commands";

function posToOffset(doc, line, ch) {
  // CM5 lines are 0-based, CM6 are 1-based
  const l = doc.line(Math.max(1, Math.min(doc.lines, line + 1)));
  if (ch == null || Number.isNaN(ch))
    ch = 0;
  return Math.max(l.from, Math.min(l.to, l.from + ch));
}

function offsetToPos(doc, offset) {
  const l = doc.lineAt(offset);
  return { line: l.number - 1, ch: offset - l.from };
}

/** Add a CM5-style TextMarker decoration (className / title / tilde attrs). */
const addMarkEffect = StateEffect.define();
/** Clear one mark produced by markText (value = Decoration range). */
const clearMarkEffect = StateEffect.define();

/**
 * Holds markText decorations. Must be in the editor's extension list
 * (see codemirrorBoot createEditor).
 */
export const cmMarkField = StateField.define({
  create() {
    return Decoration.none;
  },
  update(marks, tr) {
    marks = marks.map(tr.changes);
    for (const e of tr.effects) {
      if (e.is(addMarkEffect))
        marks = marks.update({ add: [e.value] });
      else if (e.is(clearMarkEffect))
        marks = marks.update({
          filter: (_from, _to, value) => value !== e.value,
        });
    }
    return marks;
  },
  provide: (f) => EditorView.decorations.from(f),
});

export class CMBridge {
  constructor(view) {
    this.view = view;
    this._hitSide = false;
  }

  get state() { return this.view.state; }
  get doc() { return this.view.state.doc; }

  getCursor() {
    const pos = offsetToPos(this.doc, this.view.state.selection.main.head);
    if (this._hitSide)
      pos.hitSide = true;
    return pos;
  }

  getLine(n) {
    return this.doc.line(n + 1).text;
  }

  getValue() {
    return this.doc.toString();
  }

  lineCount() {
    return this.doc.lines;
  }

  lastLine() {
    return this.doc.lines - 1;
  }

  firstLine() {
    return 0;
  }

  setCursor(line, ch) {
    const offset = posToOffset(this.doc, line, ch ?? 0);
    this._hitSide = false;
    this.view.dispatch({ selection: { anchor: offset }, scrollIntoView: true });
  }

  setSize(width, height) {
    const dom = this.view.dom;
    if (width != null && width !== "auto")
      dom.style.width = typeof width === "number" ? `${width}px` : width;
    if (height != null && height !== "auto")
      dom.style.height = typeof height === "number" ? `${height}px` : height;
  }

  replaceSelection(text) {
    const sel = this.view.state.selection.main;
    this.view.dispatch(sel.empty
      ? { changes: { from: sel.from, insert: text }, selection: { anchor: sel.from + text.length } }
      : { changes: { from: sel.from, to: sel.to, insert: text }, selection: { anchor: sel.from + text.length } });
  }

  replaceRange(text, from, to) {
    const f = posToOffset(this.doc, from.line, from.ch);
    const t = posToOffset(this.doc, to.line, to.ch);
    this.view.dispatch({ changes: { from: f, to: t, insert: text } });
  }

  /**
   * CM5 markText — used by render.vue focus() for error underlines
   * (class erroneous-text + tilde/title attributes).
   */
  markText(from, to, options = {}) {
    let f = posToOffset(this.doc, from.line, from.ch);
    let t = posToOffset(this.doc, to.line, to.ch);
    if (f > t) [f, t] = [t, f];
    // CM6 mark decorations require a non-empty range.
    if (f === t)
      return { clear() {} };
    const attrs = { ...(options.attributes || {}) };
    if (options.title != null && attrs.title == null)
      attrs.title = options.title;
    if (options.tilde != null && attrs.tilde == null)
      attrs.tilde = options.tilde;
    const deco = Decoration.mark({
      class: options.className || "",
      attributes: attrs,
    });
    // Filter clear() by Mark identity — Range objects are remapped on edits.
    const range = deco.range(f, t);
    this.view.dispatch({ effects: addMarkEffect.of(range) });
    return {
      clear: () => {
        this.view.dispatch({
          effects: clearMarkEffect.of(deco),
        });
      },
    };
  }

  /** CM5 addSelection — extend multi-selection (error highlight path). */
  addSelection(anchor, head) {
    const a = posToOffset(this.doc, anchor.line, anchor.ch);
    const h = head != null ? posToOffset(this.doc, head.line, head.ch) : a;
    const cur = this.view.state.selection;
    const next = EditorSelection.create(
      [...cur.ranges, EditorSelection.range(a, h)],
      cur.ranges.length,
    );
    this.view.dispatch({ selection: next });
  }

  moveH(dir, unit) {
    if (unit !== "char") return;
    const head = this.view.state.selection.main.head;
    const target = dir < 0 ? Math.max(0, head - 1) : Math.min(this.doc.length, head + 1);
    this._hitSide = target === head;
    if (this._hitSide) return;
    this.view.dispatch({ selection: { anchor: target } });
  }

  moveV(dir, unit) {
    const head = this.view.state.selection.main.head;
    const curLine = this.doc.lineAt(head);
    if (unit === "line") {
      const targetLineNum = dir > 0 ? curLine.number + 1 : curLine.number - 1;
      if (targetLineNum < 1 || targetLineNum > this.doc.lines) {
        this._hitSide = true;
        return;
      }
      this._hitSide = false;
      const targetLine = this.doc.line(targetLineNum);
      const ch = head - curLine.from;
      this.view.dispatch({ selection: { anchor: targetLine.from + Math.min(ch, targetLine.length) } });
    } else if (unit === "page") {
      // Page up/down: move ~18 lines
      const targetLineNum = dir > 0 ? curLine.number + 18 : curLine.number - 18;
      const clamped = Math.max(1, Math.min(this.doc.lines, targetLineNum));
      this._hitSide = clamped === curLine.number;
      if (this._hitSide) return;
      const targetLine = this.doc.line(clamped);
      const ch = head - curLine.from;
      this.view.dispatch({ selection: { anchor: targetLine.from + Math.min(ch, targetLine.length) } });
    }
  }

  focus() {
    this.view.focus();
  }

  getWrapperElement() {
    return this.view.dom;
  }

  getOption(name) {
    if (name === 'indentUnit') return 2;
    return undefined;
  }

  extendSelection(pos) {
    const offset = typeof pos === 'number' ? pos : posToOffset(this.doc, pos.line, pos.ch);
    this.view.dispatch({ selection: EditorSelection.range(this.view.state.selection.main.head, offset) });
  }

  deleteH(dir, unit) {
    if (unit !== "char") return;
    const sel = this.view.state.selection.main;
    const target = dir < 0 ? Math.max(0, sel.from - 1) : sel.to + 1;
    this.view.dispatch({ changes: { from: dir < 0 ? target : sel.from, to: dir < 0 ? sel.from : target }, selection: { anchor: target }, userEvent: "delete" });
  }

  showHint() {
    startCompletion(this.view);
  }

  toggleComment() {
    toggleComment(this.view);
  }

  addLineClass(line, where, className) {
    // CM6 uses Decorations for line classes; store for a StateField
    if (!this._lineClasses) this._lineClasses = new Map();
    const key = `${line}:${where}`;
    if (!this._lineClasses.has(key)) this._lineClasses.set(key, new Set());
    this._lineClasses.get(key).add(className);
    this._applyLineClasses();
  }

  removeLineClass(line, where, className) {
    if (!this._lineClasses) return;
    const key = `${line}:${where}`;
    const set = this._lineClasses.get(key);
    if (set) {
      set.delete(className);
      if (set.size === 0) this._lineClasses.delete(key);
    }
    this._applyLineClasses();
  }

  _applyLineClasses() {
    // Simple approach: directly add/remove CSS classes on the DOM line elements
    // CM6 line elements have data attributes; we query by line number
    if (!this._lineClasses) return;
    const gutter = this.view.dom.querySelectorAll('.cm-gutters .cm-gutterElement');
    for (const [key, classes] of this._lineClasses) {
      const [line, where] = key.split(':');
      const idx = parseInt(line);
      if (where === 'gutter' && gutter[idx]) {
        for (const cls of classes) {
          gutter[idx].classList.add(cls);
        }
      }
    }
  }

  getTokenAt(pos) {
    // CM6 doesn't have a direct equivalent; use the stream language's token info
    // For the hint function, we just need the token at the cursor position
    const offset = posToOffset(this.doc, pos.line, pos.ch);
    const line = this.doc.line(pos.line + 1);
    const before = line.text.slice(0, pos.ch);
    // Find the token at the cursor by matching word/identifier characters
    const match = before.match(/[\w.\\]+$/);
    if (match) {
      return {
        string: match[0],
        start: pos.ch - match[0].length,
        end: pos.ch,
      };
    }
    return { string: "", start: pos.ch, end: pos.ch };
  }

  // Static helper: Pos(line, ch) → {line, ch} (same as CM5)
  static Pos(line, ch) {
    return { line, ch };
  }
}

// Also export deleteToLineEnd for Alt-D
export function deleteToLineEnd(bridge) {
  const view = bridge.view;
  const sel = view.state.selection.main;
  const lastLine = view.state.doc.lines;
  const to = view.state.doc.line(lastLine).to;
  const fromLine = view.state.doc.lineAt(sel.from);
  view.dispatch({
    changes: { from: fromLine.from, to },
    selection: { anchor: fromLine.from },
    userEvent: "delete"
  });
  view.focus();
}

// Static commands object for backward compatibility
export const CodeMirror = {
  Pos: CMBridge.Pos,
  commands: {
    goDocEnd(cm) {
      const offset = cm.doc.length;
      cm.view.dispatch({ selection: { anchor: offset }, scrollIntoView: true });
    },
    goDocStart(cm) {
      cm.view.dispatch({ selection: { anchor: 0 }, scrollIntoView: true });
    },
    newlineAndIndent(cm) {
      const sel = cm.view.state.selection.main;
      const line = cm.doc.lineAt(sel.head);
      const indent = line.text.match(/^ */)[0];
      cm.replaceSelection("\n" + indent);
    },
  },
};
