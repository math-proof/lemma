import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Def.Probability.SymbolicProbability.Part2
import Theorem.Function
import Def.Probability.JointRv
import Def.Probability.Expectation
import Syntax.Probability.Probability.LiftRV
open MeasureTheory
open scoped ProbabilityTheory


/-! ### Binder notation `𝔼`

Python-aligned surface form (cf. `Expectation[x ~ D](f, given=…)` in `../py/sympy`):

* brackets = limits (integrated RV(s) before `:`, free RVs after `|`)
* parentheses = body (+ optional `given` after `|`)
* Integrated slot is `ident,+`, or a single GetElem slice `x[i]` (high-priority forms
  `𝔼[x[i]: π](…)` / conditional / partial, cf. `∑ x[t], …`): one RV is bare; two or more idents pack
  right-nested `JointRandomSymbol` (joint law). That is **not** the same as
  nested `𝔼[x: π](𝔼[y: π](…))` (product of marginals) unless independence.
  Process binders `ℕ → Ω → α` are read via `Expectation.asRV` as path RVs
  `Ω → (ℕ → α)` (e.g. `𝔼[r, s, a : M θ](…)`); ordinary RVs stay definitionally themselves.

* **Scalar (integrate out completely):**
  `𝔼[x: π](f x)` → `Expectation.ofRV π (Expectation.asRV x) …`
  `𝔼[x, y: π](f x y)` → `Expectation.ofRV π (JointRandomSymbol (Expectation.asRV x) (Expectation.asRV y)) …`
* **Scalar conditional at a fixed observation:**
  `𝔼[x: π](f x | y = y0)` / `𝔼[x, z: π](f | y = y0)` → `Expectation.condEval …`
  (`=` is evaluation of a regular conditional at the observed value, not the event `{y = y0}`)
  Joint observations: `| (y, z) = (y0, z0)` (any term on the left of `=`), or the `∧`-chain
  `| y = y0 ∧ z = z0 ∧ …` (two or more conjuncts), which conditions on the joint random variable
  `JointRandomSymbol y (JointRandomSymbol z …)` at `(y0, z0, …)`, as in `ℙ[π](… | y = y0 ∧ z = z0)`.
* **Scalar conditional given random argument(s) (no observation) = σ-algebra conditional expectation:**
  `𝔼[x: π](f x | y)` / `𝔼[x, z: π](f | y t, (u, v), w (t + 1))` / `𝔼[r: π](f | s[t], a[t])`
  → `Expectation.condSigma …`
  `= π[fun ω ↦ f (x ω) | MeasurableSpace.comap y inferInstance]` (Mathlib `condExp`; no density, no
  atoms needed; defined up to `π`-a.e. equality, so compare with `=ᵐ[π]`).
  After `|` come arbitrary terms `Ω → _` (not only names) without a top-level `=` (that would be an
  observation): one is used bare, two or more are packed right-nested by `JointRandomSymbol`
  (`y, z, w` ↦ `(y, (z, w))`; write `(y, z), w` for `((y, z), w)`). GetElem `s[t]` is allowed
  (`term:51`). The conditioners are outside the binder scope: in `𝔼[s: π](f (s t) | s t)` the
  `s t` after `|` is the random variable.
  **Nested under an outer random op that threads aliases** (today: any `𝔼[…]` elaborator
  that calls `desugarProbRA`, including partial/`| ys` forms; the walker also descends into
  arbitrary subterms such as `𝕍𝕒𝕣`/`ℂ𝕠𝕧`/`ℙ` applications): the same surface `| s[t], a[t]`
  is rewritten (with outer aliases) to `| s₀ t = s t ∧ a₀ t = a t` → `Expectation.condEval`,
  matching handwritten `have s₀ := s; have a₀ := a` — so
  `𝔼[s, a: π](𝔼[r: π](f | s[t], a[t]) • …)` (and the same nested `𝔼` under `𝕍𝕒𝕣`/`ℂ𝕠𝕧`/`ℙ`
  in that body) needs no manual aliases.
  A binder is turned into `let x := «integ».…` inside the body, so `𝔼[x: π](f x)` reads `f` at the
  *value* of `x`. That rebinding is kept when `x` is not a local (a constant such as `reward`, or a
  name introduced by the notation) and when the body uses a local `x` as that value
  (`𝔼[a: π](f a)`, `∑' t, γ ^ t * r t`). It is skipped when `x` is already a local and the body
  mentions it only as a random variable inside `ℙ` (`ℙ[π](a t = u | s t = x)`): those occurrences
  keep the outer local, so `SinglePSpace` sees `a t : Ω → _` rather than the integrated path value.
* **Random-valued (integrate out, leave other RVs free):**
  `𝔼[x: π | y]((x + y)^2)` / `𝔼[x, z: π | y](…)` → `Expectation.partialRV …`
  Any number of free RVs after `|` in the brackets.
  A currently-illegal bare form `𝔼[x: π](f x + g y)` (free RV `y` used as a sample, no `| y`
  in the brackets) elaborates as `fun ω ↦ 𝔼[x: π](f x + g (y ω))`. Existing legal scalar
  forms (`𝔼[x: π](f x)`, `𝔼[x: π](f x | s = s0)`, …) are unchanged: those are tried first.
* **Random-valued + fixed observation:**
  `𝔼[x: π | y](… | r = r0)` / joint integrate likewise → `Expectation.partialRV_cond`
  Joint observations: `| (r, s) = (r0, s0)`.
  Bare `𝔼[x: π](f x + g y | s = s0)` likewise becomes
  `fun ω ↦ 𝔼[x: π](f x + g (y ω) | s = s0)` when scalar `condEval` does not elaborate
  (e.g. `g y` with `y : Ω → _`). Only `x` is integrated; `y` is a free sample, not a
  joint integral, and the inner form does not further condition on `y`.
* There is no random-valued + random-argument form: integrate the free RVs too and condition on
  them, `𝔼[x, y: π](f x y | y, r)` (σ-algebra conditional expectation given `σ(y, r)`).
-/

/-- Measure slot of `𝔼[xs: π | ys]`: a head applied to arguments, e.g. `M θ` or `(M θ)`.
It is `term:max` followed by `term:max` arguments, none of which may start with `|`: a plain `term` slot
would let the application parser read `|y …` as Mathlib's `|x|` abs and fail instead of stopping before
the `| ys` of the bracket. (A parenthesised measure is still accepted, and an abs argument can be written
`(|c|)`.) The forms where the measure is followed directly by `]` take a full `term`. -/
syntax expectMeasure := term:max (ppSpace !"|" term:max)*

syntax:max "𝔼[" ident,+ ":" term "]" "(" term:51 ")" : term

syntax:max "𝔼[" ident,+ ":" term "]" "(" term:51 "|" term:51 "=" term:51 ")" : term

/-- `𝔼[xs : π](body | y = y0 ∧ z = z0 ∧ …)`: joint observation, at least two conjuncts (a single
`| y = y0` is the form above, so the two never overlap). -/
syntax:max "𝔼[" ident,+ ":" term "]" "(" term:51 "|" term:51 "=" term:51 "∧" sepBy1(term:51 "=" term:51, "∧") ")" : term

/-- `𝔼[xs : π](body | y₁, …, yₙ)`: σ-algebra conditional expectation `π[body | σ(y₁, …, yₙ)]`;
the `yᵢ` are arbitrary terms (random variables `Ω → _`) at precedence 51, so that an observation
`| y = y0` is never read as a conditioner; they are packed right-nested by `JointRandomSymbol`. -/
syntax:max "𝔼[" ident,+ ":" term "]" "(" term:51 "|" term:51,+ ")" : term

syntax:max "𝔼[" ident,+ ":" expectMeasure "|" ident,+ "]" "(" term:51 ")" : term

syntax:max "𝔼[" ident,+ ":" expectMeasure "|" ident,+ "]" "(" term:51 "|" term:max "=" term:51 ")" : term


syntax:max (name := varBind) "𝕍𝕒𝕣[" ident,+ ":" term "]" "(" term:51 ")" : term

/-- Internal desugar target for `𝕍𝕒𝕣[xs: π](body)` (avoids quoting the `𝕍𝕒𝕣` def). -/
syntax:max (name := varBindCore) "varBindCore%" ident,+ ":" term "in" term:51 : term




/-- Binder piece `x[i]` for integrate-slot GetElem forms. -/
syntax expectSlice := ident noWs "[" withoutPosition(term) "]"

/-- Integrate binder that is a GetElem slice `x[i]` (same spirit as `∑ x[t], …`).
High priority so `𝔼[x[i]: π](…)` is not read as `ident,+`. -/
syntax:max (name := expectAtGetElem) (priority := high)
  "𝔼[" expectSlice ":" term "]" "(" term:51 ")" : term

syntax:max (name := expectAtGetElemCond) (priority := high)
  "𝔼[" expectSlice ":" term "]" "(" term:51 "|" term:51 "=" term:51 ")" : term

syntax:max (name := expectAtGetElemCondAnd) (priority := high)
  "𝔼[" expectSlice ":" term "]" "(" term:51 "|" term:51 "=" term:51 "∧" sepBy1(term:51 "=" term:51, "∧") ")" : term

syntax:max (name := expectAtGetElemRA) (priority := high)
  "𝔼[" expectSlice ":" term "]" "(" term:51 "|" term:51,+ ")" : term

syntax:max (name := expectAtGetElemPartial) (priority := high)
  "𝔼[" expectSlice ":" expectMeasure "|" ident,+ "]" "(" term:51 ")" : term

syntax:max (name := expectAtGetElemPartialCond) (priority := high)
  "𝔼[" expectSlice ":" expectMeasure "|" ident,+ "]" "(" term:51 "|" term:max "=" term:51 ")" : term

open Lean

macro_rules (kind := varBind)
  | `(𝕍𝕒𝕣[$xs:ident,* : $π]($body)) => `(varBindCore% $xs,* : $π in $body)

/-- Local GetElem kind check (mirrors `Expectation.Macro.isGetElemKind`; kept here so
`macro_rules` for `expectAtGetElem*` stay with their `syntax` in this file). -/
def ExpectSyntax.isGetElemKind (k : SyntaxNodeKind) : Bool :=
  k == `«term__[_]» || k == `ProbabilityTheory.«term__[_]»

def ExpectSyntax.asGetElem (e : Syntax) : Option Syntax :=
  if ExpectSyntax.isGetElemKind e.getKind then
    some e
  else if e.getKind == `choice then
    let args := e.getArgs
    match args.find? (fun a => a.getKind == `«term__[_]») with
    | some g => some g
    | none => args.find? (fun a => ExpectSyntax.isGetElemKind a.getKind)
  else
    none

/-- Head `ident` and index `term` of an `expectSlice` node `x[i]`. -/
def ExpectSyntax.sliceParts (s : Syntax) : MacroM (TSyntax `ident × Term) := do
  if s.getNumArgs < 3 then
    Macro.throwError "expectSlice: expected ident [ term ]"
  pure (⟨s[0]⟩, ⟨s[2]⟩)

/-- Replace `x[t]` / `x t` in `body` by fresh `c`. -/
def ExpectSyntax.expandAtGetElem (x : TSyntax `ident) (t : Term) (body : Term) :
    MacroM (Ident × Term) := do
  let c := mkIdent (← Macro.addMacroScope `c)
  let rec go (s : Syntax) : StateM Bool Syntax := do
    match ExpectSyntax.asGetElem s with
    | some ge =>
      let coll := ge[0]
      let idx := ge[2]
      if coll.isIdent && coll.getId == x.getId && idx.structEq t.raw then
        set true
        return c.raw
      else
        match s with
        | .node info kind args => return .node info kind (← args.mapM go)
        | s => return s
    | none =>
      match s with
      | .node info kind args =>
        if kind == ``Lean.Parser.Term.app && args.size == 2 then
          let fn := args[0]!
          let argStx := args[1]!
          if fn.isIdent && fn.getId == x.getId && argStx.getNumArgs == 1 && argStx[0].structEq t.raw then
            set true
            return c.raw
          else
            return .node info kind (← args.mapM go)
        else
          return .node info kind (← args.mapM go)
      | s => return s
  let (body', found) := (go body.raw).run false
  if !found then
    Macro.throwError s!"'…[{x.getId}[_]: …](…)': the body does not contain '{x.getId}[_]' / '{x.getId} _' at the given index"
  pure (c, ⟨body'⟩)

macro_rules (kind := expectAtGetElem)
  | `(𝔼[$s:expectSlice : $π]($body)) => do
      let (x, t) ← ExpectSyntax.sliceParts s.raw
      let (c, body') ← ExpectSyntax.expandAtGetElem x t body
      let rhs ← `($x[$t])
      `(let $c := $rhs; 𝔼[$c:ident : $π]($body'))

macro_rules (kind := expectAtGetElemCond)
  | `(𝔼[$s:expectSlice : $π]($body | $y:term = $y0)) => do
      let (x, t) ← ExpectSyntax.sliceParts s.raw
      let (c, body') ← ExpectSyntax.expandAtGetElem x t body
      let rhs ← `($x[$t])
      `(let $c := $rhs; 𝔼[$c:ident : $π]($body' | $y = $y0))

macro_rules (kind := expectAtGetElemCondAnd)
  | `(𝔼[$s:expectSlice : $π]($body | $y:term = $y0:term ∧ $[$ys:term = $ys0:term]∧*)) => do
      let (x, t) ← ExpectSyntax.sliceParts s.raw
      let (c, body') ← ExpectSyntax.expandAtGetElem x t body
      let rhs ← `($x[$t])
      `(let $c := $rhs; 𝔼[$c:ident : $π]($body' | $y = $y0 ∧ $[$ys:term = $ys0:term]∧*))

macro_rules (kind := expectAtGetElemRA)
  | `(𝔼[$s:expectSlice : $π]($body | $ys,*)) => do
      let (x, t) ← ExpectSyntax.sliceParts s.raw
      let (c, body') ← ExpectSyntax.expandAtGetElem x t body
      let rhs ← `($x[$t])
      `(let $c := $rhs; 𝔼[$c:ident : $π]($body' | $ys,*))

macro_rules (kind := expectAtGetElemPartial)
  | `(𝔼[$s:expectSlice : $π:expectMeasure | $ys,*]($body)) => do
      let (x, t) ← ExpectSyntax.sliceParts s.raw
      let (c, body') ← ExpectSyntax.expandAtGetElem x t body
      let rhs ← `($x[$t])
      `(let $c := $rhs; 𝔼[$c:ident : $π | $ys,*]($body'))

macro_rules (kind := expectAtGetElemPartialCond)
  | `(𝔼[$s:expectSlice : $π:expectMeasure | $ys,*]($body | $r:term = $r0)) => do
      let (x, t) ← ExpectSyntax.sliceParts s.raw
      let (c, body') ← ExpectSyntax.expandAtGetElem x t body
      let rhs ← `($x[$t])
      `(let $c := $rhs; 𝔼[$c:ident : $π | $ys,*]($body' | $r = $r0))

syntax:max (name := varAtGetElem) (priority := high)
  "𝕍𝕒𝕣[" expectSlice ":" term "]" "(" term:51 ")" : term

macro_rules (kind := varAtGetElem)
  | `(𝕍𝕒𝕣[$s:expectSlice : $π]($body)) => do
      let (x, t) ← ExpectSyntax.sliceParts s.raw
      let (c, body') ← ExpectSyntax.expandAtGetElem x t body
      let rhs ← `($x[$t])
      `(let $c := $rhs; 𝕍𝕒𝕣[$c:ident : $π]($body'))


/-- Right-nested `JointRandomSymbol` chain of `Expectation.asRV` binders:
`#[x,y,z]` ↦ `JointRandomSymbol (Expectation.asRV x) (JointRandomSymbol (Expectation.asRV y) (Expectation.asRV z))`.
One element returns `Expectation.asRV y` (ordinary RV or flipped process path). -/
partial def Expectation.Macro.mkRestJoint (ys : Array Syntax) : MacroM Term := do
  match ys.toList with
  | [] => Macro.throwError "𝔼[…](…) requires at least one random variable in this slot"
  | [y] =>
    let y : Term := ⟨y⟩
    `(Expectation.asRV $y)
  | y :: rest =>
    let y : Term := ⟨y⟩
    let tail ← Expectation.Macro.mkRestJoint rest.toArray
    `(JointRandomSymbol (Expectation.asRV $y) $tail)

/-- Right-nested `JointRandomSymbol` chain of arbitrary conditioning terms (no `asRV`):
`#[y, z, w]` ↦ `JointRandomSymbol y (JointRandomSymbol z w)`; one term is returned bare. -/
partial def Expectation.Macro.mkJointTerms (ys : Array Syntax) : MacroM Term := do
  match ys.toList with
  | [] => Macro.throwError "𝔼[…](… | …) requires at least one conditioning term"
  | [y] => pure ⟨y⟩
  | y :: rest =>
    let y : Term := ⟨y⟩
    let tail ← Expectation.Macro.mkJointTerms rest.toArray
    `(JointRandomSymbol $y $tail)

/-- Unpack a right-nested product into `let y := nest.1; …; body`.
`rebind[i] = false` skips the `let` for that binder (the body keeps the outer local).
`asFun[i] = true` wraps the value path as `Fun.mk`, so `y[t]` stays `Fun` indexing. -/
partial def Expectation.Macro.unpackRest
    (ys : Array Syntax) (nest : Term) (body : Term) (rebind : Array Bool) (asFun : Array Bool) : MacroM Term := do
  let bind (y : Ident) (rhs : Term) (funProcess : Bool) (body : Term) : MacroM Term :=
    if funProcess then `(let $y := Fun.mk $rhs; $body) else `(let $y := $rhs; $body)
  match ys.toList, rebind.toList, asFun.toList with
  | [], _, _ => pure body
  | [y], r :: _, f :: _ =>
    if r then
      bind ⟨y⟩ nest f body
    else
      pure body
  | y :: rest, r :: rs, f :: fs =>
    let nest2 ← `(Prod.snd $nest)
    let body' ← Expectation.Macro.unpackRest rest.toArray nest2 body rs.toArray fs.toArray
    if r then
      bind ⟨y⟩ (← `(Prod.fst $nest)) f body'
    else
      pure body'
  | _, [], _ => Macro.throwError "𝔼 binder unpack: rebind mask shorter than the binder list"
  | _, _, [] => Macro.throwError "𝔼 binder unpack: Fun mask shorter than the binder list"

/-- The measure term of an `expectMeasure` slot: `f a b` ↦ the application `f a b`. -/
def Expectation.Macro.measure (π : TSyntax `expectMeasure) : MacroM Term :=
  match π with
  | `(expectMeasure| $f:term $[$args:term]*) =>
    if args.isEmpty then pure f else `($f $args*)
  | _ => Macro.throwUnsupported
