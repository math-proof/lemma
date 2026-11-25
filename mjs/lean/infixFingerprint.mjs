/**
 * Readable form of a fingerprint tree. The stored JSON is unchanged.
 * `T(x)` is the postfix transpose `xᵀ`, and `Inv(x)` is `x⁻¹`.
 */

/** Tighter operators bind first. `assoc` decides which side keeps its parentheses. */
const INFIX = {
  Pow: { op: '^', prec: 85, assoc: 'right' },
  SMul: { op: '•', prec: 83, assoc: 'left' },
  Dot: { op: '⬝', prec: 82, assoc: 'left' },
  Mul: { op: '*', prec: 80, assoc: 'left' },
  Div: { op: '/', prec: 80, assoc: 'left' },
  SDiff: { op: '\\', prec: 80, assoc: 'left' },
  Add: { op: '+', prec: 70, assoc: 'left' },
  Sub: { op: '-', prec: 70, assoc: 'left' },
  Union: { op: '∪', prec: 70, assoc: 'left' },
  Append: { op: '++', prec: 65, assoc: 'right' },
  Cons: { op: '::', prec: 65, assoc: 'right' },
  Construct: { op: '::', prec: 65, assoc: 'right' },
  Eq: { op: '=', prec: 50, assoc: 'none' },
  Ne: { op: '≠', prec: 50, assoc: 'none' },
  Lt: { op: '<', prec: 50, assoc: 'none' },
  Gt: { op: '>', prec: 50, assoc: 'none' },
  Le: { op: '≤', prec: 50, assoc: 'none' },
  Ge: { op: '≥', prec: 50, assoc: 'none' },
  HEq: { op: '≍', prec: 50, assoc: 'none' },
  In: { op: '∈', prec: 50, assoc: 'none' },
  Subset: { op: '⊆', prec: 50, assoc: 'none' },
  Supset: { op: '⊇', prec: 50, assoc: 'none' },
  Colon: { op: ':', prec: 40, assoc: 'none' },
  And: { op: '∧', prec: 35, assoc: 'right' },
  Cond: { op: '|', prec: 32, assoc: 'left' },
  Or: { op: '∨', prec: 30, assoc: 'right' },
  Iff: { op: '↔', prec: 20, assoc: 'none' },
};

const PREFIX = {
  Sqrt: { op: '√', prec: 88 },
  Neg: { op: '-', prec: 75 },
  Not: { op: '¬', prec: 60 },
};

/** Quantifier or big operator: `∀ binder, body`, `∑ binder, body`. */
const BINDER = {
  All: '∀',
  Exists: '∃',
  Sum: '∑',
  Prod: '∏',
  Integral: '∫',
};

/** `‖x‖`, `|x|`, `⌈x⌉`, `{a, b}`, and a joint `(a, b)`. The delimiters group the inside. */
const DELIM = {
  Norm: ['‖', '‖'],
  Abs: ['|', '|'],
  Ceil: ['⌈', '⌉'],
  Floor: ['⌊', '⌋'],
  Card: ['|', '|'],
  Brace: ['{', '}'],
  Joint: ['(', ')'],
};

/** `Icc a b` is `[a, b]`, `Ico` is `[a, b)`, `Ioc` is `(a, b]`, `Ioo` is `(a, b)`. */
const INTERVAL = {
  Icc: ['[', ']'],
  Ico: ['[', ')'],
  Ioc: ['(', ']'],
  Ioo: ['(', ')'],
};

/** `∇[x] body`, `∂[x] body`, `ℙ[π] event`, `𝔼[x] body`. */
const INDEXED = {
  Grad: '∇',
  Deriv: '∂',
  Prob: 'ℙ',
  Expect: '𝔼',
};

const CALL = 90;
const ATOM = 100;
const POST = 85;

function side(child, prec, which, assoc) {
  if (child.prec > prec) return child.text;
  if (child.prec < prec) return `(${child.text})`;
  if (assoc === 'left' && which === 'left') return child.text;
  if (assoc === 'right' && which === 'right') return child.text;
  return `(${child.text})`;
}

function chain(spec, children) {
  let acc = children[0];
  for (let i = 1; i < children.length; i++) {
    const left = side(acc, spec.prec, 'left', spec.assoc);
    const right = side(children[i], spec.prec, 'right', spec.assoc);
    acc = { text: `${left} ${spec.op} ${right}`, prec: spec.prec };
  }
  return acc;
}

/** `[i < n, j < m] body`. A multi-index bound is stored as `And`, printed with commas. */
function stackText(rawChildren) {
  const domain = rawChildren[0];
  const bounds = domain && typeof domain === 'object' && !Array.isArray(domain) && Object.keys(domain)[0] === 'And'
    ? (Array.isArray(domain.And) ? domain.And : [domain.And])
    : [domain];
  const items = bounds.map((part) => infix(part).text).filter(Boolean).join(', ');
  const body = rawChildren.slice(1).map(infix).filter((part) => part.text)
    .map((part) => part.text)
    .join(', ');
  return { text: body ? `[${items}] ${body}` : `[${items}]`, prec: 10 };
}

function postfix(arg, op, prec = POST) {
  const text = arg.prec < prec ? `(${arg.text})` : arg.text;
  return { text: text + op, prec };
}

function delimited(open, close, children) {
  return { text: `${open}${children.map((part) => part.text).join(', ')}${close}`, prec: ATOM };
}

function indexed(op, children) {
  if (!children.length) return { text: op, prec: 10 };
  const [head, ...rest] = children;
  const body = rest
    .map((part) => (part.prec < CALL ? `(${part.text})` : part.text))
    .join(', ');
  return { text: body ? `${op}[${head.text}] ${body}` : `${op}[${head.text}]`, prec: 10 };
}

/** One tree, or one line per tree when a step stored several. */
export function infixFingerprint(json) {
  if (Array.isArray(json)) return json.map((tree) => infix(tree).text).filter(Boolean).join('\n');
  return infix(json).text;
}

function infix(json) {
  if (json == null || json === '') return { text: '', prec: ATOM };
  if (typeof json === 'string') return { text: json, prec: ATOM };
  if (Array.isArray(json)) {
    const parts = json.map(infix).filter((part) => part.text);
    return { text: parts.map((part) => part.text).join('\n'), prec: 0 };
  }
  const head = Object.keys(json)[0];
  const rawChildren = Array.isArray(json[head]) ? json[head] : [json[head]];
  if (head === 'Stack') return stackText(rawChildren);
  const children = rawChildren.map(infix).filter((part) => part.text);
  const delim = DELIM[head];
  if (delim) return delimited(delim[0], delim[1], children);
  const span = INTERVAL[head];
  if (span && children.length === 2) {
    return { text: `${span[0]}${children[0].text}, ${children[1].text}${span[1]}`, prec: ATOM };
  }
  const indexedOp = INDEXED[head];
  if (indexedOp) return indexed(indexedOp, children);
  const infixOp = INFIX[head];
  if (infixOp && children.length >= 2) return chain(infixOp, children);
  const prefix = PREFIX[head];
  if (prefix && children.length === 1) {
    const arg = children[0].prec < prefix.prec ? `(${children[0].text})` : children[0].text;
    return { text: prefix.op + arg, prec: prefix.prec };
  }
  if ((head === 'Square' || head === 'Cube') && children.length === 1) {
    return postfix(children[0], head === 'Square' ? '²' : '³');
  }
  if (head === 'T' && children.length === 1) return postfix(children[0], 'ᵀ');
  if (head === 'Inv' && children.length === 1) return postfix(children[0], '⁻¹', CALL);
  if (head === 'Get' && children.length >= 2) {
    const [base, ...idx] = children;
    const b = base.prec < CALL ? `(${base.text})` : base.text;
    return { text: `${b}[${idx.map((part) => part.text).join(', ')}]`, prec: CALL };
  }
  if (head === 'Fun' && children.length >= 2) {
    const [dom, ...rest] = children;
    return { text: `${dom.text} ↦ ${rest.map((part) => part.text).join(', ')}`, prec: 10 };
  }
  const binder = BINDER[head];
  if (binder && children.length >= 2) {
    const [dom, ...rest] = children;
    return { text: `${binder} ${dom.text}, ${rest.map((part) => part.text).join(', ')}`, prec: 10 };
  }
  if (binder && children.length === 1) return { text: `${binder} ${children[0].text}`, prec: 10 };
  return { text: `${head}(${children.map((part) => part.text).join(', ')})`, prec: CALL };
}
