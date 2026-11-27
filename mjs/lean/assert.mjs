import { Lean } from '../../js/parser/lean.js';

/** Echo reprint: `@[path]` on the lemma becomes `@[path, axioms]` so Lean logs axiom use. Source `.lean` is unchanged. */
export function withEchoAxiomsAttr(code) {
  return String(code).replace(/^([ \t]*)@\[([^\]]*)\][ \t]*$/gm, (line, indent, inner) => {
    const parts = inner.split(',').map((s) => s.trim()).filter(Boolean);
    if (!parts.includes('path') || parts.includes('axioms')) return line;
    return `${indent}@[${[...parts, 'axioms'].join(', ')}]`;
  });
}

export function traceEchoSource(tree) {
  const source = String(tree);
  let prefix = '\uE000node';
  while (source.includes(prefix)) prefix += '_';

  // Include structural nodes that specialized traverse() methods may skip.
  const parents = new Map();
  function visit(node, parent = null) {
    if (!(node instanceof Lean) || parents.has(node)) return;
    parents.set(node, parent);
    for (const child of node.args ?? []) visit(child, node);
  }
  visit(tree);

  const nodes = [...parents.keys()];
  const marker = new RegExp(prefix + '(\\d+)([BSE])\uE001', 'g');
  const restore = [];
  let marked;
  try {
    nodes.forEach((node, index) => {
      const original = node.toString;
      const descriptor = Object.getOwnPropertyDescriptor(node, 'toString');
      Object.defineProperty(node, 'toString', {
        configurable: true,
        value(...args) {
          const text = original.apply(this, args);
          if (node instanceof Lean.classes.LeanCaret && parents.get(node) === tree && text === '') {
            return prefix + index + 'B\uE001';
          }
          // Child markers do not contribute to a parent's rendered span.
          const visible = text.replace(marker, token => ' '.repeat(token.length));
          const start = visible.search(/\S/u);
          if (start === -1) return text;
          const end = visible.trimEnd().length;
          return text.slice(0, start) + prefix + index + 'S\uE001' +
            text.slice(start, end) + prefix + index + 'E\uE001' + text.slice(end);
        },
      });
      restore.push(() => {
        if (descriptor) Object.defineProperty(node, 'toString', descriptor);
        else delete node.toString;
      });
    });
    marked = String(tree);
  } finally {
    for (const reset of restore) reset();
  }

  return { source, marked, nodes, parents, marker };
}

/** Check the generated-source coordinates against the marked render, line by line. */
export function assertEchoSourceLines(tree, codeStr, trace = traceEchoSource(tree)) {
  const { source, marked, nodes, parents, marker } = trace;
  const problems = [];
  const spans = new Map();
  const open = new Map();
  const blankLines = new Map();
  const unmarked = marked.split('\n').map((line, index) => line.replace(marker, (_, id, edge) => {
    const node = nodes[Number(id)];
    const lineNumber = index + 1;
    if (edge === 'B') {
      blankLines.set(node, lineNumber);
    } else if (edge === 'S') {
      if (open.has(node)) throw new Error('Overlapping Echo AST spans for ' + node.constructor.name);
      open.set(node, lineNumber);
    } else {
      const start = open.get(node);
      if (start === undefined) throw new Error('Missing Echo AST span start on line ' + lineNumber);
      if (!spans.has(node)) spans.set(node, []);
      spans.get(node).push({ start, end: lineNumber });
      open.delete(node);
    }
    return '';
  })).join('\n');
  if (open.size) throw new Error('Unclosed Echo AST spans');

  if (unmarked !== source || withEchoAxiomsAttr(unmarked) !== codeStr) {
    throw new Error('Echo AST tracing changed the rendered source');
  }

  const fileLines = codeStr.split('\n').length;
  const anchors = new Map();
  const finalNode = tree.args.at(-1);
  const eofCaret = finalNode instanceof Lean.classes.LeanCaret ? finalNode : null;
  let lastLine = Lean.lastSourceLine(tree);
  for (const node of nodes) {
    const height = node.height;
    const occurrences = spans.get(node) ?? [];
    const actual = node.line;
    const anchor = occurrences[0]?.start ?? anchors.get(parents.get(node)) ?? 1;
    anchors.set(node, anchor);
    if (height === 0 && occurrences.length === 0) {
      const expected = blankLines.get(node) ?? (node === eofCaret ? fileLines : anchor);
      if (actual !== expected) {
        problems.push(node.constructor.name + ' stamped ' + actual + ', empty at ' + expected);
      }
      continue;
    }
    if (!occurrences.length) {
      problems.push(node.constructor.name + ' has height ' + height + ' but no rendered span');
      continue;
    }
    for (const { start, end } of occurrences) {
      if (actual !== start || height !== end - start + 1) {
        problems.push(node.constructor.name + ' stamped ' + actual + ' with height ' +
          height + ', rendered on lines ' + start + '–' + end);
      }
    }
    if (Number.isInteger(actual)) lastLine = Math.max(lastLine, actual + height - 1);
  }

  if (problems.length || lastLine !== fileLines) {
    throw new Error(
      'Echo line assertion: ' + problems.length + ' node mismatches; AST last line ' +
      lastLine + ', file lines ' + fileLines + '\n' + problems.slice(0, 20).join('\n'),
    );
  }
}
