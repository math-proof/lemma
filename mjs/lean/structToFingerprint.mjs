/**
 * Convert the Lean `Expr.toJson` structural tree (the `struct` field emitted by
 * `Echo` next to `expr.toLatex` of the same expression) into the search
 * fingerprint tree that `conclusionSearchJson` / `toJSON({ leaves, binders })` produce.
 *
 * Output shape matches `js/parser/lean/*` `toJSON`:
 *   - nodes: `{ Head: [children] }`
 *   - leaves: `"$n"` (free name, numbered by first appearance), `"?n"`
 *     (De Bruijn, `?0` nearest), numerals (`"0"`, `"1"`), or `""` (dropped).
 *
 * The Lean and JS trees are produced from different provenance (elaborated
 * `Lean.Expr` vs source syntax), so this is a best-effort tree mapping:
 *   - types, `sort`, and instances are dropped, mirroring the source fingerprint
 *   - implicit coercions (`Fin.val`, `Nat.cast`, …) are erased
 *   - elaboration artefacts (`Slice.mk`, `GetElem.getElem`, `Prod.mk`,
 *     `True.intro`) are folded into their surface form (`Slice`, `Get`, tuple)
 *   - `kind: "lemma"` is an axiom or theorem application, so the node is a proof
 *     and is omitted. `⟨i, by tactic⟩ : Fin _` (`Subtype.mk` / `Fin.mk`) keeps `i` only
 * Unknown heads fall back to the capitalized last name segment so the result is
 * always a well-formed fingerprint tree.
 */

/** Lean name -> JS `pathToken` for infix kinds handled by name. */
const KIND_HEAD = {
  eq: 'Eq',
  ne: 'Ne',
  lt: 'Lt',
  gt: 'Gt',
  le: 'Le',
  ge: 'Ge',
  and: 'And',
  or: 'Or',
  iff: 'Iff',
  cons: 'Construct',
  mem: 'In',
};

/** `limits` op -> JS head (`Lean_sum` -> `Sum`, …). */
const LIMIT_HEAD = {
  sum: 'Sum',
  tsum: 'Tsum',
  prod: 'Prod',
  int: 'Integral',
  bigcup: 'Bigcup',
  bigcap: 'Bigcap',
  lim: 'Lim',
  sup: 'Sup',
  inf: 'Inf',
  max: 'Max',
  min: 'Min',
};

/** `method` name -> JS head. */
const METHOD_HEAD = {
  prob: 'Prob',
  condProb: 'Prob',
  expect: 'Expect',
  var: 'Var',
  deriv: 'Deriv',
  grad: 'Grad',
  integral: 'Integral',
};

/** Coercions introduced by elaboration; the source fingerprint never has them. */
const ERASED_PREFIX = new Set([
  'Fin.val',
  'Nat.cast',
  'Int.cast',
  'Rat.cast',
  'Real.cast',
  'ENNReal.ofReal',
  'Complex.ofReal',
  'SetLike.coe',
  'Coe.coe',
]);

/** prefix/postfix op last segment -> JS head. */
const OP_HEAD = {
  neg: 'Neg',
  inv: 'Inv',
  abs: 'Abs',
  sqrt: 'Sqrt',
  factorial: 'Factorial',
  transpose: 'Transpose',
  adjoint: 'Adjoint',
};

const lastSegment = (name) => String(name ?? '').split('.').pop() || '';
const cap = (s) => (s ? s.charAt(0).toUpperCase() + s.slice(1) : '');
// Subscript digits/letters (U+2080–U+209C, U+1D62–U+1D6A, U+2C7C). Superscripts
// are notation (`x²` = `x ^ 2`), so they are not part of a variable name.
const SUBSCRIPT_TAIL = /[\u2080-\u2089\u2090-\u209C\u1D62-\u1D6A\u2C7C]+$/u;
// A single letter plus its subscript is a variable, never a global function
// head: `r`, `rₐ`, `Rₘ`, and the ASCII form `A_length`, `a_min`, `a_t`, `𝒮_0`.
const isVariableHead = (s) => {
  const raw = String(s ?? '');
  const base = raw.replace(SUBSCRIPT_TAIL, '');
  if ([...base].length === 1 && /\p{L}/u.test(base)) return true;
  return /^\p{L}_\S+$/u.test(raw);
};
const isNumeral = (s) => /^\d+$/.test(s);
// JS only binds plain identifiers; `«\sf{a}»` / `c✝` stay free leaves.
const isBinderName = (s) => /^[\p{L}_][\p{L}\p{N}_]*$/u.test(s);

/** Free/bound/numeric leaf, mirroring `LeanToken.toJSON` (atomic.js). */
function leaf(text, ctx) {
  const name = String(text ?? '');
  if (name === '') return '';
  if (isNumeral(name)) return name;
  for (let i = ctx.binders.length - 1; i >= 0; i--) {
    if (ctx.binders[i] === name) return `?${ctx.binders.length - 1 - i}`;
  }
  if (!ctx.leaves.has(name)) ctx.leaves.set(name, ctx.leaves.size + 1);
  return `$${ctx.leaves.get(name)}`;
}

/** `Head(a)(b)`-style node. */
function node(head, children) {
  return { [head]: children };
}

/** `HAdd.hAdd` -> `Add`, `Union.union` -> `Union`, `Set.Subset` -> `Subset`. */
function infixHead(op) {
  const seg = lastSegment(op);
  if (/^h[A-Z]/.test(seg)) return seg.slice(1);
  return cap(seg);
}

/** `x ^ 2` / `x ^ 3` mirror the `x²` / `x³` notation heads. */
function power(struct, ctx) {
  const [base, exp] = struct.args ?? [];
  const b = base == null ? '' : convert(base, ctx);
  const e = exp == null ? '' : convert(exp, ctx);
  if (e === '2') return node('Square', [b]);
  if (e === '3') return node('Cube', [b]);
  return node('Pow', [b, e]);
}

/** Is this a bare `∑ i` / `∀ i` domain rather than `∈ s` / `: T`? */
function isUniv(type) {
  if (!type || type.kind === 'nil') return true;
  if (type.kind !== 'const') return false;
  return /(^|\.)(univ|Finset\.univ|Set\.univ)$/.test(String(type.value ?? ''));
}

/** Domain JSON for one binder, mirroring `jsonBinderDomain`:
 *  the set/type is converted *before* the binder is pushed (so a free `$n`),
 *  the bound variable *after* (so `?0`). */
function binderDomain(binder, ctx) {
  const name = String(binder.name ?? '');
  const type = binder.type ?? null;
  const bound = isBinderName(name);
  if (binder.binder === 'contains' && !isUniv(type)) {
    const rhs = convert(type, ctx);
    if (bound) ctx.binders.push(name);
    return { In: [leaf(name, ctx), rhs] };
  }
  if (binder.binder !== 'contains' && !isUniv(type)) {
    const rhs = convert(type, ctx);
    if (bound) ctx.binders.push(name);
    return { Colon: [leaf(name, ctx), rhs] };
  }
  if (bound) ctx.binders.push(name);
  return leaf(name, ctx);
}

/** `∀`/`∃`/`fun`/big operators: domains first, then the scoped body. */
function quantified(kind, struct, ctx) {
  // JS parses `fun i => body` as `{Fun: [?0, body]}`: the lambda pushes its
  // plain-identifier binders, so both the binder and its occurrences in the
  // body are De Bruijn leaves. `Fun` is a plain n-ary head — the arrow is only
  // the class-level inner structure (`LeanRightarrow`), not a JSON node.
  if (kind === 'fun') {
    const depth = ctx.binders.length;
    try {
      const args = [];
      for (const binder of struct.binders ?? []) {
        const name = String(binder.name ?? '');
        if (!name) continue;
        if (isBinderName(name)) ctx.binders.push(name);
        args.push(leaf(name, ctx));
      }
      args.push(convert(struct.body, ctx));
      return { Fun: args };
    } finally {
      ctx.binders.length = depth;
    }
  }
  const head = kind === 'forall' ? 'All' : kind === 'exists' ? 'Any' : LIMIT_HEAD[struct.op] ?? cap(struct.op);
  // The JS fingerprint folds directly nested same-head big operators into one
  // node whose domains are conjoined innermost-first (`∑ i ∈ s, ∑ j ∈ t, f`);
  // elaboration keeps them as nested `Finset.sum` applications.
  const binders = [];
  let bodyStruct;
  if (kind === 'limits') {
    bodyStruct = struct;
    while (bodyStruct?.kind === 'limits' && bodyStruct.op === struct.op) {
      binders.push(...(bodyStruct.args ?? []).slice(1));
      bodyStruct = bodyStruct.args?.[0];
    }
  } else {
    binders.push(...(struct.binders ?? []));
    bodyStruct = struct.body;
  }
  const depth = ctx.binders.length;
  try {
    const domains = binders.map((binder) => binderDomain(binder, ctx));
    const body = convert(bodyStruct, ctx);
    const args = [];
    if (domains.length > 1) args.push({ And: domains.reverse() });
    else if (domains.length === 1) args.push(domains[0]);
    if (body !== '') args.push(body);
    return node(head, args);
  } finally {
    ctx.binders.length = depth;
  }
}

/** `∫⁻ a, body ∂μ` / `∫ a, body ∂μ`: elaborated as `lintegral μ (fun a => body)`.
 *  The JS fingerprint keeps the bound variable as the domain and drops the
 *  measure argument entirely. */
function integralApplication(args, ctx) {
  const fn = args[1];
  if (fn?.kind !== 'fun') {
    return node('Integral', [convert(args[0], ctx), convert(fn, ctx)]);
  }
  const binders = fn.binders ?? [];
  const depth = ctx.binders.length;
  try {
    for (const binder of binders) {
      const name = String(binder.name ?? '');
      if (isBinderName(name)) ctx.binders.push(name);
    }
    const domain = binders.length ? leaf(binders[0].name, ctx) : '';
    return node('Integral', [domain, convert(fn.body, ctx)]);
  } finally {
    ctx.binders.length = depth;
  }
}

/** Application forms: mimic `LeanArgsSpaceSeparated.toJSON`. */
function application(name, args, ctx) {
  // `x[:k]` and `y[t]` are notations in the source; elaboration exposes the
  // implementation constants, which fold back to `Get`.
  if (name === 'Function.getSlice' || (name === 'JointRandomSymbol' && (args ?? []).length >= 3)) {
    return node('Get', [convert(args[0], ctx), convert(args[1], ctx)]);
  }
  if (name === 'JointRandomSymbol') return (args ?? []).map((arg) => convert(arg, ctx));
  if (name === 'Expectation.condRV') {
    return node('CondRV', (args ?? []).map((arg) => convert(arg, ctx)));
  }
  if (/^(MeasureTheory\.(lintegral|integral)|intervalIntegral\.integral)$/.test(name)) {
    return integralApplication(args, ctx);
  }
  const seg = lastSegment(name);
  if (isVariableHead(seg)) return '_';
  return node(cap(seg), (args ?? []).map((arg) => convert(arg, ctx)));
}

function special(struct, ctx) {
  const op = String(struct.op ?? '');
  const args = struct.args ?? [];
  // Plain space-separated application: multi-letter heads keep the
  // capitalised name (`range x` → `Range(x)`); single letters are variables
  // and stay anonymous (`r x` → `_`), like `LeanArgsSpaceSeparated.toJSON`.
  if (op === '[anonymous]') {
    const head = args[0];
    if (!head) return '';
    const name = String(head.name ?? head.op ?? '');
    if (isVariableHead(name)) return '_';
    return node(cap(lastSegment(name) || 'Anonymous'), args.slice(1).map((arg) => convert(arg, ctx)));
  }
  if (op === 'Prod.mk') return args.map((arg) => convert(arg, ctx));
  if (op === 'Slice.mk') {
    const lo = args[0];
    const step = args[2];
    const from = lo?.kind === 'const' && lo.value === '0' ? '' : convert(lo, ctx);
    const to = args[1] == null ? '' : convert(args[1], ctx);
    const keepStep = step != null && !(step.kind === 'const' && step.value === '1');
    return node('Slice', keepStep ? [from, to, convert(step, ctx)] : [from, to]);
  }
  if (op === 'GetElem.getElem') {
    return node('Get', [convert(args[0], ctx), convert(args[1], ctx)]);
  }
  if (op === 'OfNat.ofNat' && args[0]?.kind === 'const' && isNumeral(String(args[0].value))) {
    return String(args[0].value);
  }
  return node(cap(lastSegment(op)), args.map((arg) => convert(arg, ctx)));
}

function prefixOrPostfix(struct, ctx) {
  const op = String(struct.op ?? '');
  const args = struct.args ?? [];
  const seg = lastSegment(op);
  if (ERASED_PREFIX.has(op) || seg === 'coe' || seg === 'cast') {
    return args[0] == null ? '' : convert(args[0], ctx);
  }
  const head = OP_HEAD[seg] ?? cap(seg);
  return node(head, args.map((arg) => convert(arg, ctx)));
}

/** `x[:k]` / `y[t]` / `(a, s)` encodings of random variables. */
function randomValues(struct, ctx) {
  if (struct?.kind === 'operatorname' && struct.name === 'JointRandomSymbol') {
    return (struct.args ?? []).map((arg) => convert(arg, ctx));
  }
  if (struct?.kind === 'special' && struct.op === 'Prod.mk') {
    return (struct.args ?? []).map((arg) => convert(arg, ctx));
  }
  return [convert(struct, ctx)];
}

/** `ℙ[π](a = x | s = y)` stores the joint RV and the point as tuples. */
function eventPairs(rv, point, ctx) {
  const left = randomValues(rv, ctx);
  const right = randomValues(point, ctx);
  return left.map((lhs, i) => node('Eq', [lhs, right[i] ?? '']));
}

/**
 * `Expr.toJson` stores a method's arguments in Lean order, with `idx` the
 * self parameter. `toLatex` prints `args.swap 0 idx`, receiver first
 * (`d, a` at idx 1 → `a.natAdd d`). The fingerprint uses that printed order.
 */
function receiverFirst(args, idx) {
  const copy = [...(args ?? [])];
  const i = Number(idx);
  if (!Number.isInteger(i) || i <= 0 || i >= copy.length) return copy;
  const self = copy[i];
  copy[i] = copy[0];
  copy[0] = self;
  return copy;
}

function method(struct, ctx) {
  const name = String(struct.name ?? '');
  const seg = lastSegment(name);
  const args = struct.args ?? [];
  if (seg === 'condProb') {
    const measure = convert(args[0], ctx);
    return node('Prob', [measure, node('Cond', eventPairs(args[1], args[2], ctx))]);
  }
  const head = METHOD_HEAD[seg] ?? cap(seg);
  return node(head, receiverFirst(args, struct.idx).map((arg) => convert(arg, ctx)));
}

/** Notation the parser fingerprints structurally instead of by head:
 *  `Membership.mem S a` is `a ∈ S` → `In(a)(S)` (arguments flipped),
 *  `Insert.insert a (Singleton.singleton b)` is `{a, b}` → `Brace(a)(b)`,
 *  `Singleton.singleton a` is `{a}` → `Brace(a)`.
 *  Member and element are converted in source order so `$n` numbering matches. */
function setNotation(struct, ctx) {
  if (struct.op === 'Membership.mem') {
    const [set, member] = struct.args ?? [];
    const a = member == null ? '' : convert(member, ctx);
    const s = set == null ? '' : convert(set, ctx);
    return node('In', [a, s]);
  }
  if (struct.op === 'Singleton.singleton') {
    const [value] = struct.args ?? [];
    return node('Brace', [value == null ? '' : convert(value, ctx)]);
  }
  if (struct.op === 'Insert.insert') {
    const [head, tail] = struct.args ?? [];
    if (tail?.op === 'Singleton.singleton') {
      const [value] = tail.args ?? [];
      const a = head == null ? '' : convert(head, ctx);
      const b = value == null ? '' : convert(value, ctx);
      return node('Brace', [a, b]);
    }
  }
  return null;
}

/**
 * `⟨i, by tactic⟩ : Fin _` elaborates as `Subtype.mk` or `Fin.mk`.
 * The property argument is a proof and is not part of the formula.
 */
function finElement(struct) {
  const name = String(struct?.name ?? struct?.op ?? '');
  if (name !== 'Subtype.mk' && name !== 'Fin.mk') return undefined;
  const args = struct.args ?? [];
  return args.length ? args[0] : null;
}

/**
 * `Name.is_Lemma`: the constant is an axiom or a theorem (`thmInfo` / `axiomInfo`).
 * Applying it produces a proof, so the node is not part of the formula.
 */
function omittedProof(struct) {
  return struct?.kind === 'lemma';
}

/** Single entry point: convert one `Expr.toJson` node. */
export function convert(struct, ctx = { leaves: new Map(), binders: [] }) {
  if (struct == null) return '';
  if (typeof struct === 'string') return struct;
  if (omittedProof(struct)) return '';
  const element = finElement(struct);
  if (element !== undefined) return element == null ? '' : convert(element, ctx);
  const notation = setNotation(struct, ctx);
  if (notation) return notation;
  const kind = struct.kind;
  switch (kind) {
    case 'nil':
    case 'sort':
      return '';
    case 'const':
      // `Complex.I` elaborates to the constant `Complex.ImaginaryUnit`; it is a
      // nullary definition like `0` / `1`, so it is a literal leaf, not a name.
      if (struct.value === 'ImaginaryUnit') return 'I';
      return leaf(struct.value, ctx);
    case 'symbol':
      return leaf(struct.name, ctx);
    case 'binder':
      return String(struct.name ?? '') ? leaf(struct.name, ctx) : '';
    case 'forall':
    case 'exists':
    case 'fun':
    case 'limits':
      return quantified(kind, struct, ctx);
    case 'eq':
    case 'ne':
    case 'lt':
    case 'gt':
    case 'le':
    case 'ge':
    case 'and':
    case 'or':
    case 'iff':
    case 'cons':
    case 'mem':
      return node(KIND_HEAD[kind], (struct.args ?? []).map((arg) => convert(arg, ctx)));
    case 'infix':
    case 'prop_infix':
      if (struct.op === 'HPow.hPow') return power(struct, ctx);
      return node(infixHead(struct.op), (struct.args ?? []).map((arg) => convert(arg, ctx)));
    case 'prefix':
    case 'postfix':
      return prefixOrPostfix(struct, ctx);
    case 'special':
      return special(struct, ctx);
    case 'method':
      return method(struct, ctx);
    case 'property':
      return node(cap(lastSegment(struct.name)), (struct.args ?? []).map((arg) => convert(arg, ctx)));
    case 'operatorname':
    case 'function':
    case 'typeclass':
    case 'lemma':
      return application(struct.name, struct.args, ctx);
    default: {
      const name = lastSegment(struct.name ?? struct.op ?? kind);
      if (Array.isArray(struct.args)) return node(cap(name), struct.args.map((arg) => convert(arg, ctx)));
      return name ? leaf(name, ctx) : '';
    }
  }
}

/** Fingerprint tree (`{ Head: [...] }`) for a Lean `Expr.toJson` tree. */
export function structToFingerprint(struct) {
  return convert(struct, { leaves: new Map(), binders: [] });
}
