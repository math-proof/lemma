// Assignments the stock UMD bundle does not put on the constructor.
// Vendored ESM fork: static/codemirror/lib/codemirror.js sets
// CodeMirror.clipPos and CodeMirror.deleteNearSelection.
//
// clipPos + clipToLen copied from static/codemirror/src/line/pos.js
// getLine copied from static/codemirror/src/line/utils_line.js
// deleteNearSelection copied from static/codemirror/src/edit/deleteNearSelection.js
// cmp copied from static/codemirror/src/line/pos.js
// lst copied from static/codemirror/src/util/misc.js
// runInOp is cm.operation. replaceRange is doc.replaceRange. Both call the
// same stock closures. ensureCursorVisible writes curOp.scrollToPos with the
// same fields as static/codemirror/src/display/highlight_worker.js.

function getLine(doc, n) {
  n -= doc.first
  if (n < 0 || n >= doc.size) throw new Error("There is no line " + (n + doc.first) + " in the document.")
  let chunk = doc
  while (!chunk.lines) {
    for (let i = 0;; ++i) {
      let child = chunk.children[i], sz = child.chunkSize()
      if (n < sz) { chunk = child; break }
      n -= sz
    }
  }
  return chunk.lines[n]
}

function cmp(a, b) { return a.line - b.line || a.ch - b.ch }

function lst(arr) { return arr[arr.length - 1] }

function clipToLen(Pos, pos, linelen) {
  let ch = pos.ch
  if (ch == null || ch > linelen) return Pos(pos.line, linelen)
  else if (ch < 0) return Pos(pos.line, 0)
  else return pos
}

function clipPos(doc, pos) {
  const Pos = clipPos.Pos
  if (pos.line < doc.first) return Pos(doc.first, 0)
  let last = doc.first + doc.size - 1
  if (pos.line > last) return Pos(last, getLine(doc, last).text.length)
  return clipToLen(Pos, pos, getLine(doc, pos.line).text.length)
}

function deleteNearSelection(cm, compute) {
  let ranges = cm.doc.sel.ranges, kill = []
  // Build up a set of ranges to kill first, merging overlapping
  // ranges.
  for (let i = 0; i < ranges.length; i++) {
    let toKill = compute(ranges[i])
    while (kill.length && cmp(toKill.from, lst(kill).to) <= 0) {
      let replaced = kill.pop()
      if (cmp(replaced.from, toKill.from) < 0) {
        toKill.from = replaced.from
        break
      }
    }
    kill.push(toKill)
  }
  // Next, remove those actual ranges.
  cm.operation(() => {
    for (let i = kill.length - 1; i >= 0; i--)
      cm.doc.replaceRange("", kill[i].from, kill[i].to, "+delete")
    let cur = cm.getCursor()
    cm.curOp.scrollToPos = {from: cur, to: cur, margin: cm.options.cursorScrollMargin}
  })
}

export function installCodeMirrorExtras() {
  const CodeMirror = window.CodeMirror
  if (!CodeMirror) throw new Error("CodeMirror global missing")
  clipPos.Pos = CodeMirror.Pos
  CodeMirror.clipPos = clipPos
  CodeMirror.deleteNearSelection = deleteNearSelection
}
