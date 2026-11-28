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
  // Named argument `(m := d)`. Looser than application, so it is parenthesized as an argument.
  Assign: { op: ':=', prec: 15, assoc: 'none' },
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

/**
 * Numeric binders stop before `=` (`∑ i, f i = 0` parses as `(∑ i, f i) = 0`,
 * verified with Lean), so they need no parentheses next to a comparison. The
 * logical binders keep precedence 10: `∃ x, P x ∧ Q` swallows the `∧`.
 */
const NUMERIC_BINDER_PREC = 60;
const NUMERIC_BINDERS = new Set(['Sum', 'Prod', 'Integral']);

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
const POST = 95;

const SUBSCRIPT = '₀₁₂₃₄₅₆₇₈₉';

/**
 * Display form of a stored variable leaf: `$n` (free, numbered by first
 * appearance) → `fₙ`, `?n` (De Bruijn bound) → `bₙ`. Anonymous leaves (`_`)
 * and numerals are unchanged.
 */
function leafText(text) {
  const match = /^([$?])(\d+)$/.exec(text);
  if (!match) return text;
  const digits = [...match[2]].map((digit) => SUBSCRIPT[Number(digit)]).join('');
  return (match[1] === '?' ? 'b' : 'f') + digits;
}

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

function stackText(rawChildren) {
  const domain = rawChildren[0];
  const body = rawChildren.slice(1).map((part) => infix(part)).filter((part) => part.text)
    .map((part) => part.text)
    .join(', ');
  const andBounds =
    domain && typeof domain === 'object' && !Array.isArray(domain) && Object.keys(domain)[0] === 'And'
      ? (Array.isArray(domain.And) ? domain.And : [domain.And])
      : null;
  let head;
  if (andBounds && andBounds.length > 1) {
    // And is innermost-first; Lean source order is outer-to-inner.
    head = [...andBounds].reverse()
      .map((part) => infix(part).text)
      .filter(Boolean)
      .map((text) => `[${text}]`)
      .join('');
  } else {
    const bounds = andBounds
      ?? (Array.isArray(domain) ? domain : [domain]);
    const items = bounds.map((part) => infix(part).text).filter(Boolean).join(', ');
    head = `[${items}]`;
  }
  return { text: body ? `${head} ${body}` : head, prec: 10 };
}

function postfix(arg, op, prec = POST) {
  // An application argument gets parentheses (`(RotaryOn f g)ᵀ`).
  const text = arg.prec <= CALL ? `(${arg.text})` : arg.text;
  return { text: text + op, prec };
}

function delimited(open, close, children) {
  return { text: `${open}${children.map((part) => part.text).join(', ')}${close}`, prec: ATOM };
}

/**
 * Lean application is left-associative juxtaposition: `f a b` means `(f a) b`,
 * but an application argument needs parentheses: `f a (g b)`.
 * A head keeps its parentheses only when it is looser than application
 * (`(a + b) c`). A bare constant is an atom, so `f g` stays unparenthesized.
 */
function parenthesize(part, asHead) {
  if (!part?.text) return '';
  const wrap = asHead ? part.prec < CALL : part.prec <= CALL;
  return wrap ? `(${part.text})` : part.text;
}

function indexed(op, children) {
  if (!children.length) return { text: op, prec: 10 };
  const [head, ...rest] = children;
  const body = rest.map((part) => parenthesize(part, false)).join(', ');
  return { text: body ? `${op}[${head.text}] ${body}` : `${op}[${head.text}]`, prec: 10 };
}

/** One tree, or one line per tree when a step stored several. Renders free
 * leaves `$n` as `fₙ` and bound leaves `?n` as `bₙ`, with Lean-like
 * application juxtaposition. A nested application argument is parenthesized
 * (`f a (g b)`); a bare constant argument is not (`f g`).
 */
export function infixFingerprint(json) {
  if (Array.isArray(json)) return json.map((tree) => infix(tree).text).filter(Boolean).join('\n');
  return infix(json).text;
}

function infix(json) {
  if (json == null || json === '') return { text: '', prec: ATOM };
  if (typeof json === 'string') return { text: leafText(json), prec: ATOM };
  if (Array.isArray(json)) {
    // A plain array is one expression applied to arguments
    // (e.g. `(Matrix.rotaryOn u v θ).transpose i j`). First element is the
    // head expression, rest are arguments — all space-separated.
    const parts = json.map((part) => infix(part)).filter((part) => part.text);
    if (parts.length > 1) {
      return {
        text: parts.map((part, i) => parenthesize(part, i === 0)).join(' '),
        prec: CALL,
      };
    }
    if (parts.length === 1) return parts[0];
    return { text: '', prec: 0 };
  }
  const head = Object.keys(json)[0];
  const rawChildren = Array.isArray(json[head]) ? json[head] : [json[head]];
  if (head === 'Stack') return stackText(rawChildren);
  const children = rawChildren.map((part) => infix(part)).filter((part) => part.text);
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
    // Indexing binds tighter than application, so `f a[i]` needs no parentheses.
    return { text: `${parenthesize(base, false)}[${idx.map((part) => part.text).join(', ')}]`, prec: POST };
  }
  if (head === 'Fun' && rawChildren.length >= 2) {
    const binders = rawChildren.slice(0, -1);
    // A binder slot is recorded at its point of introduction. Display its
    // index at the lambda body, where the final binder has index zero.
    const names = binders.map((binder, i) => binder === '?0'
      ? leafText(`?${binders.slice(i + 1).filter(next => next === '?0').length}`)
      : infix(binder).text);
    const body = infix(rawChildren.at(-1));
    return { text: `fun ${names.join(' ')} ↦ ${body.text}`, prec: 10 };
  }
  if (head === 'Ite' && children.length >= 2) {
    const [cond, thenPart, elsePart] = children;
    const body = elsePart
      ? `if ${cond.text} then ${thenPart.text} else ${elsePart.text}`
      : `if ${cond.text} then ${thenPart.text}`;
    return { text: `(${body})`, prec: ATOM };
  }
  const binder = BINDER[head];
  const binderPrec = NUMERIC_BINDERS.has(head) ? NUMERIC_BINDER_PREC : 10;
  if (binder && children.length >= 2) {
    const [dom, ...rest] = children;
    return { text: `${binder} ${dom.text}, ${rest.map((part) => part.text).join(', ')}`, prec: binderPrec };
  }
  if (binder && children.length === 1) return { text: `${binder} ${children[0].text}`, prec: binderPrec };
  // Plain application is Lean juxtaposition. A nested application is an
  // argument, so it is parenthesized (`Reindex (FinSumFinEquiv …) …`).
  // A bare constant stays an atom (`f g`, not `f (g)`).
  const args = children.map((part) => parenthesize(part, false)).join(' ');
  return { text: args ? `${head} ${args}` : head, prec: args ? CALL : ATOM };
}
