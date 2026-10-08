import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import sympy.stats.symbolic_probability
open MeasureTheory
open scoped ProbabilityTheory


/--
[sympy.JointRandomSymbol](https://github.com/sympy/sympy/blob/master/sympy/stats/joint_rv.py)
-/
def JointRandomSymbol
    {Ω α β : Type*}
    (x : Ω → α) (y : Ω → β) :
    Ω → α × β :=
  fun ω ↦ (x ω, y ω)


/--
Pointwise coercion of a pair of functions on the same domain to a function into pairs:
`↑(x, y) = JointRandomSymbol x y`. A bare pair `(x, y)` is therefore accepted
wherever an `Ω → α × β` is expected — e.g. `let prod : Ω → α × β := (x, y)` — and the
`CoeFun` instance also makes application `(x, y) ω` well-typed. The coe body delegates
to `JointRandomSymbol` (rather than re-using an anonymous `fun`) so typeclass search
sees the same head symbol: e.g. a hypothesis written as a bare pair `(x, y)`
also supplies `SinglePSpace π (x, y)`.
-/
instance Function.coeProdPi {ι α β : Type*} :
    Coe ((ι → α) × (ι → β)) (ι → α × β) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩

instance Function.coeFunProdPi {ι α β : Type*} :
    CoeFun ((ι → α) × (ι → β)) (fun _ => ι → α × β) :=
  ⟨fun p ↦ JointRandomSymbol p.1 p.2⟩


/--
Triple variants: a nested pair of functions on the same domain coerces in one step to a
function into nested pairs, in both associations. Coercions do not chain through nested
`Prod.mk` nodes at argument positions, so a bare `((x, y), z)` or `(x, (y, z))` needs these
instances to be accepted where an `Ω → (α × β) × γ` (resp. `Ω → α × (β × γ)`) is expected.
-/
instance Function.coeProdPi3L {ι α β γ : Type*} :
    Coe (((ι → α) × (ι → β)) × (ι → γ)) (ι → (α × β) × γ) :=
  ⟨fun p ↦ JointRandomSymbol (JointRandomSymbol p.1.1 p.1.2) p.2⟩

instance Function.coeProdPi3R {ι α β γ : Type*} :
    Coe ((ι → α) × ((ι → β) × (ι → γ))) (ι → α × (β × γ)) :=
  ⟨fun p ↦ JointRandomSymbol p.1 (JointRandomSymbol p.2.1 p.2.2)⟩

instance Function.coeFunProdPi3L {ι α β γ : Type*} :
    CoeFun (((ι → α) × (ι → β)) × (ι → γ)) (fun _ => ι → (α × β) × γ) :=
  ⟨fun p ↦ JointRandomSymbol (JointRandomSymbol p.1.1 p.1.2) p.2⟩

instance Function.coeFunProdPi3R {ι α β γ : Type*} :
    CoeFun ((ι → α) × ((ι → β) × (ι → γ))) (fun _ => ι → α × (β × γ)) :=
  ⟨fun p ↦ JointRandomSymbol p.1 (JointRandomSymbol p.2.1 p.2.2)⟩


/--
Unconditional expectation of an ordinary observable of a random variable:

  `Expectation.ofRV π x f = expectation (π.map x) f`

Here `f : α → β` is a normal function on the *value* of `x : Ω → α`. Writing
`f (x ω)` (i.e. `f ∘ x`) is the random quantity whose mean this returns — the
usual “apply `f` to the RV `x`” reading.
-/
noncomputable def Expectation.ofRV
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace α]
    [Expectation β]
    (π : Measure Ω)
    (x : Ω → α)
    [PSpace π x]
    (f : α → β) :
    β :=
  expectation (π.map x) f


/--
Conditional expectation of an ordinary observable of `x` given `y = y0`:

  `Expectation.condRV π x y f y0
    = expectation (ReferenceMeasure.measure.withDensity
        (fun a ↦ π.condProb (x, y) (a, y0))) f`

Same “`f` on values of `x`” reading as `ofRV`, under the conditional law of `x`
given `y = y0`. -/
noncomputable def Expectation.condRV
    {Ω α γ β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ]
    [Expectation β]
    (π : Measure Ω)
    (x : Ω → α) (y : Ω → γ)
    [SinglePSpace π (x, y)]
    (f : α → β)
    (y0 : γ) :
    β :=
  expectation
    (ReferenceMeasure.measure.withDensity fun a ↦
      π.condProb (x, y) (a, y0))
    f

/--
Conditional expectation of an ordinary observable of `x` given the event `y = y0`, under the
conditional law `(π[|y ⁻¹' {y0}]).map x`. Needs no density: `x` can be a reward, a path, ...;
`y` is meant to be discrete so that `{y = y0}` is an event. At an event of probability `0` the
conditional measure is `0`, so the value is `0`. This is the meaning of `𝔼[x: π](f x | y = y0)`. -/
noncomputable def Expectation.condEvent
    {Ω α γ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    [Expectation β]
    (π : Measure Ω)
    (x : Ω → α) (y : Ω → γ)
    (f : α → β)
    (y0 : γ) :
    β :=
  expectation ((ProbabilityTheory.cond π (y ⁻¹' {y0})).map x) f

/--
σ-algebra conditional expectation of an observable of `x` given the random variable `y`:

  `Expectation.condSigma π x y f = π[fun ω ↦ f (x ω) | σ(y)]`,  `σ(y) = MeasurableSpace.comap y inferInstance`

i.e. Mathlib's `MeasureTheory.condExp` (defined up to `π`-a.e. equality, so it is compared with `=ᵐ[π]`).
Unlike the event form `condEvent` it needs no atoms (`y` may be continuous) and, unlike `condRV`, no densities. This is the meaning of
`𝔼[x: π](f x | y)` and `𝔼[x: π](f x | y, z, …)`. -/
noncomputable def Expectation.condSigma
    {Ω α γ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace γ]
    [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β]
    (π : Measure Ω)
    (x : Ω → α) (y : Ω → γ)
    (f : α → β) :
    Ω → β :=
  MeasureTheory.condExp (MeasurableSpace.comap y inferInstance) π (fun ω ↦ f (x ω))


/--
Partial / “leave other RVs free” expectation in `x`.

For each outcome `ω`, this is the conditional expectation of `f (·) (y ω)` given
`y = y ω`:

  `(Expectation.partialRV π x y f) ω
      = Expectation.condRV π x y (fun a ↦ f a (y ω)) (y ω)`

So the result is still a random variable `Ω → β` (a function of `y`, and of any
other randomness folded into `y`). Textbook writing like `E_x[(x+y)²]` that
returns an expression in `y` matches this when `y` is named after `|`.
-/
noncomputable def Expectation.partialRV
    {Ω α γ β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ]
    [Expectation β]
    (π : Measure Ω)
    (x : Ω → α) (y : Ω → γ)
    [SinglePSpace π (x, y)]
    (f : α → γ → β) :
    Ω → β :=
  fun ω ↦ Expectation.condRV π x y (fun a ↦ f a (y ω)) (y ω)

/--
Random-valued partial expectation in `x`, further conditioned on a fixed
observation `r = r0`.

For each `ω`:

  `(Expectation.partialRV_cond π x y r f r0) ω
      = expectation (conditional law of `x` given `y = y ω` and `r = r0`)
          (fun a ↦ f a (y ω))`

So the result is still `Ω → β` (depends on the free RVs in `y`), while `r` is
pinned to the observed value `r0`.
-/
noncomputable def Expectation.partialRV_cond
    {Ω α γ ρ β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ] [ReferenceMeasure ρ]
    [Expectation β]
    (π : Measure Ω)
    (x : Ω → α) (y : Ω → γ) (r : Ω → ρ)
    [SinglePSpace π (x, y, r)]
    (f : α → γ → β)
    (r0 : ρ) :
    Ω → β :=
  fun ω ↦
    expectation
      (ReferenceMeasure.measure.withDensity fun a ↦
        π.condProb (x, y, r) (a, (y ω, r0)))
      (fun a ↦ f a (y ω))

/--
Random-valued partial expectation in `x`, conditioned on random argument(s) `r`
(no fixed observation). Free RVs in `y` stay free in the body; `r` only conditions.
For each `ω`:

  `(Expectation.partialRV_RA π x y r f) ω
      = Expectation.partialRV_cond π x y r f (r ω) ω`

Density-based and pointwise; it has no binder sugar (the bracket form `𝔼[x: π | y](body | r, s)` was
removed on 2026-10-06). Its density-free σ-algebra analogue is `𝔼[x, y: π](f x y | y, r)`
(`Expectation.condSigma`), which agrees with it `π`-a.e. when the densities exist.
-/
noncomputable def Expectation.partialRV_RA
    {Ω α γ ρ β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ] [ReferenceMeasure ρ]
    [Expectation β]
    (π : Measure Ω)
    (x : Ω → α) (y : Ω → γ) (r : Ω → ρ)
    [SinglePSpace π (x, y, r)]
    (f : α → γ → β) :
    Ω → β :=
  fun ω ↦ Expectation.partialRV_cond π x y r f (r ω) ω

/-! ### Path-valued reading of time-indexed processes

A binder `x` in `𝔼[x: π](…)` is turned into an `Ω → _` random variable by
`Expectation.asRV` (`AsPathRV`). Ordinary RVs `x : Ω → α` stay themselves (reducible);
a process `X : ℕ → Ω → α` flips to the path-valued RV `fun ω t ↦ X t ω`. That lets one write

  `𝔼[s, a, r : M θ](∑' t, γ ^ t * r t)`

for the joint law of the three infinite-horizon processes (still a *finite* `JointRandomSymbol`
of path RVs), with `s`, `a`, `r` bound in the body as values of type `ℕ → _`.
-/

/--
Interpret a binder as an `Ω → α` random variable.

* `Ω → α` — identity (ordinary RV);
* `ℕ → Ω → α` — flip to the path `ω ↦ (t ↦ X t ω)` (process / infinite family of coordinates).

The process instance is higher priority so it wins on the overlap
`ℕ → Ω → α = (ℕ → (Ω → α))`, which also matches the identity instance with domain `ℕ`.
-/
class AsPathRV (X : Type*) (Ω : outParam Type*) (α : outParam Type*) where
  /-- Underlying `Ω → α` random variable for binder `X`. -/
  path : X → Ω → α

/-- Ordinary random variable: binder is already `Ω → α`. -/
@[reducible]
instance (priority := 100) AsPathRV.ofFunction {Ω α : Type*} : AsPathRV (Ω → α) Ω α where
  path f := f

/-- Time-indexed process: binder `X` becomes the path-valued RV `fun ω t ↦ X t ω`. -/
@[reducible]
instance (priority := 1000) AsPathRV.process {Ω α : Type*} :
    AsPathRV (ℕ → Ω → α) Ω (ℕ → α) where
  path f := fun ω t ↦ f t ω

/-- `AsPathRV.path` is the identity on an ordinary random variable. -/
@[simp] theorem AsPathRV.path_function {Ω α : Type*} (f : Ω → α) :
    AsPathRV.path f = f :=
  rfl

/-- `AsPathRV.path` flips a process to its path-valued random variable. -/
@[simp] theorem AsPathRV.path_process {Ω α : Type*} (X : ℕ → Ω → α) :
    AsPathRV.path X = fun ω t ↦ X t ω :=
  rfl

/--
Transparent binder coercion used by the `𝔼` macro.

Reducible so that for an ordinary RV `x : Ω → α` one has `Expectation.asRV x = x`
(definitionally), and proofs that rewrite with `π.map x` keep working. For a process
`X : ℕ → Ω → α`, this is the path `fun ω t ↦ X t ω`.
-/
@[reducible, inline]
def Expectation.asRV {X : Type*} {Ω α : Type*} [AsPathRV X Ω α] (x : X) : Ω → α :=
  AsPathRV.path x

@[simp] theorem Expectation.asRV_function {Ω α : Type*} (f : Ω → α) :
    Expectation.asRV f = f :=
  rfl

@[simp] theorem Expectation.asRV_process {Ω α : Type*} (X : ℕ → Ω → α) :
    Expectation.asRV X = fun ω t ↦ X t ω :=
  rfl

/-- Left operand of the `⟂ᵢ` sugar: a process `X : ℕ → Ω → α` (e.g. a slice `r[t + 1:]`) becomes
its path-valued RV `Expectation.asRV X = fun ω k ↦ X k ω`; any other term is returned unchanged
(syntactically, so `rw`/`simp` patterns on ordinary RVs keep matching). -/
syntax (name := condIndepLeft) "condIndepLeft% " term:max : term

open Lean Elab Term Meta in
@[term_elab condIndepLeft] def elabCondIndepLeft : TermElab := fun stx _ => do
  match stx with
  | `(condIndepLeft% $x) =>
    let e ← Lean.Elab.Term.elabTerm x none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty ← whnfR (← instantiateMVars (← inferType e))
    match ty with
    | .forallE _ d b _ =>
      if d.isConstOf ``Nat && !b.hasLooseBVars && (← whnfR b).isForall then
        mkAppM ``Expectation.asRV #[e]
      else
        return e
    | _ => return e
  | _ => throwUnsupportedSyntax

open Lean Meta Elab Tactic in
/-- `measurable_component` closes a goal `Measurable z` with a component of a local (possibly
∀-quantified) joint measurability hypothesis, e.g. `h : ∀ t, Measurable (r t, s t, a t)` (a tuple of RVs
elaborates through `Function.coeProdPi*` to `JointRandomSymbol …`): it tries `(h …).fst`, `(h …).snd`,
`(h …).snd.fst`, `(h …).snd.snd`, `(h …).fst.fst`, `(h …).fst.snd`, the arguments of `h` being found by
unification. Used by the `⟂ᵢ` sugar after `assumption` / `apply_assumption`. -/
elab "measurable_component" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let paths : List (List Name) :=
    [[``Measurable.fst], [``Measurable.snd],
     [``Measurable.snd, ``Measurable.fst], [``Measurable.snd, ``Measurable.snd],
     [``Measurable.fst, ``Measurable.fst], [``Measurable.fst, ``Measurable.snd]]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then continue
    for path in paths do
      let s ← saveState
      try
        let (xs, _, body) ← forallMetaTelescope (← instantiateMVars ldecl.type)
        unless body.isAppOf ``Measurable do throwError "not a measurability hypothesis"
        let mut pf := mkAppN ldecl.toExpr xs
        for n in path do
          pf ← mkAppM n #[pf]
        if ← isDefEq (← inferType pf) target then
          let pf' ← instantiateMVars pf
          unless pf'.hasExprMVar do
            goal.assign pf'
            replaceMainGoal []
            return
        s.restore
      catch _ => s.restore
  throwError "measurable_component: the goal is not a component of a joint measurability hypothesis"

set_option quotPrecheck false in
/-- CondIndepFun sugar: `X ⟂ᵢ[π] Y | Z` is `CondIndepFun (σ(Z)) _ X Y π`.

Precedence 100 beats Mathlib’s `x ⟂ᵢ[π] y` (50) so the trailing `| z` is not left
behind. The proof of `Measurable Z` is found by `assumption` (a local `hz`) or `apply_assumption`
(e.g. `h : ∀ t, Measurable (s t)` for `Z = s (t + 1)`), or by `measurable_component` as a component
of a (∀-quantified) joint measurability hypothesis (e.g. `h : ∀ t, Measurable (r t, s t, a t)`).
If the left operand is a process
`ℕ → Ω → α`, such as the slice `r[t + 1:]`, it is read through `Expectation.asRV` as the
path-valued RV `fun ω k ↦ r (t + 1 + k) ω`; an ordinary RV `x : Ω → α` is left untouched. -/
notation:100 X:100 " ⟂ᵢ[" μ "] " Y:100 " | " Z:100 =>
  ProbabilityTheory.CondIndepFun
    (MeasurableSpace.comap Z inferInstance)
    (Measurable.comap_le (by
      first
      | assumption
      | apply_assumption
      | measurable_component : Measurable Z))
    (condIndepLeft% X) Y μ

/-! ### Functions of random variables: `rv%[μ] x` and `x =ᵐ[μ] y`

`V t (s t) =ᵐ[π] …` (with `V t : S → ℝ` and the random variable `s t : Ω → S`) is read as
`(fun ω ↦ V t (s t ω)) =ᵐ[π] …`. -/

open Lean in
/-- Identifiers occurring in a syntax tree (deduplicated, first occurrence first). -/
partial def LiftRV.idents (stx : Syntax) (acc : Array Ident := #[]) : Array Ident :=
  if stx.isIdent then
    if acc.any (·.getId == stx.getId) then acc else acc.push ⟨stx⟩
  else
    stx.getArgs.foldl (fun acc a => LiftRV.idents a acc) acc

open Lean Meta in
/-- `some false` if `ty` is `Ω → α` (a random variable on `Ω`), `some true` if it is an indexed family
`ℕ → Ω → α` or `Fin n → Ω → α` (a process), `none` otherwise. -/
def LiftRV.kind (Ω ty : Expr) : MetaM (Option Bool) := withNewMCtxDepth do
  match ← whnf ty with
  | .forallE _ d b _ =>
    if b.hasLooseBVars then return none
    if ← isDefEq d Ω then return some false
    let d ← whnf d
    unless d.isConstOf ``Nat || d.isAppOfArity ``Fin 1 do return none
    match ← whnf b with
    | .forallE _ d' b' _ =>
      if !b'.hasLooseBVars && (← isDefEq d' Ω) then return some true else return none
    | _ => return none
  | _ => return none

open Lean Elab Term Meta in
/-- Fallback of `rv%[μ] x`: elaborate `fun ω ↦ let s := fun k ↦ s k ω; …; x` (`let x := x ω` for a plain
random variable `x`) for the local random variables / processes on `Ω` (from `μ : Measure Ω`) named in
`x`, then inline exactly these `let`s (beta-reducing `(fun k ↦ s k ω) t` to `s t ω`), so the result is
syntactically the hand-written `fun ω ↦ …`. -/
def LiftRV.lift (μ x : Term) (expectedType? : Option Expr) : TermElabM Expr := withFreshMacroScope do
  let μe ← Lean.Elab.Term.elabTerm μ none
  let μty ← whnf (← instantiateMVars (← inferType μe))
  unless μty.isAppOfArity ``MeasureTheory.Measure 2 do throwError "rv%: {μe} is not a measure"
  let Ω := μty.appFn!.appArg!
  let mut binds : Array (Ident × Bool) := #[]
  for id in LiftRV.idents x do
    let some (fv, []) ← resolveLocalName id.getId | continue
    if let some proc ← LiftRV.kind Ω (← instantiateMVars (← inferType fv)) then
      binds := binds.push (id, proc)
  if binds.isEmpty then throwError "rv%: no random variable on {Ω} to lift in {x}"
  let mut body : Term := x
  for (id, proc) in binds.reverse do
    body ← if proc then `(let $id := fun k ↦ $id k ω; $body) else `(let $id := $id ω; $body)
  let e ← Lean.Elab.Term.elabTerm (← `(fun (ω : $(← exprToSyntax Ω)) ↦ $body)) expectedType?
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let e ← lambdaBoundedTelescope e 1 fun xs b => do
    let mut b := b
    for _ in binds do
      match b with
      | .letE _ _ v b' _ => b := b'.instantiateBetaRevRange 0 1 #[v]
      | _ => throwError "rv%: unexpected elaboration result {b}"
    mkLambdaFVars xs b
  match e with
  | .lam _ t b bi => return .lam `ω t b bi
  | e => return e

/--
`rv%[μ] x` reads `x` as a random variable on `Ω` (`μ : Measure Ω`), lifting a function applied to
random variables pointwise:

* `rv%[π] (V t (s t))` ↦ `fun ω ↦ V t (s t ω)` (`V t : S → ℝ`, `s : ℕ → Ω → S`);
* `rv%[π] (Q t (s t) (a t))` ↦ `fun ω ↦ Q t (s t ω) (a t ω)`;
* `rv%[π] (u X)` ↦ `fun ω ↦ u (X ω)` (`X : Ω → α`).

`x` is first elaborated as is (normal elaboration order, postponement passed through); only if that
throws an error are the local names of type `Ω → α`, `ℕ → Ω → α` or `Fin n → Ω → α` occurring in `x`
rebound to their values at `ω`. If that fails too, the original error is rethrown. So every `x`
that already elaborates (e.g. `fun ω ↦ V t (s t ω)`, `𝔼[r: π](… | s t)`, `0`) is unchanged.
It is applied to both sides of `=ᵐ[μ]` (see the `macro_rules` below), e.g.
`∀ t, V t (s t) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t)`.
-/
syntax (name := liftRV) "rv%[" term "] " term:max : term

open Lean Elab Term Meta in
@[term_elab liftRV] def elabLiftRV : TermElab := fun stx expectedType? => do
  match stx with
  | `(rv%[$μ] $x) =>
    let saved ← saveState
    try
      withoutErrToSorry (Lean.Elab.Term.elabTerm x expectedType?)
    catch ex =>
      if let .internal id _ := ex then
        if id == postponeExceptionId then throw ex
      let failed ← saveState
      saved.restore
      try
        LiftRV.lift μ x expectedType?
      catch _ =>
        failed.restore
        throw ex
  | _ => throwUnsupportedSyntax

-- `f =ᵐ[μ] g` (Mathlib's `Filter.EventuallyEq (ae μ) f g`) with both sides read through `rv%[μ]`,
-- e.g. `V t (s t) =ᵐ[π] …` is `(fun ω ↦ V t (s t ω)) =ᵐ[π] …`.
macro_rules
  | `($f =ᵐ[$μ] $g) => `(Filter.EventuallyEq (MeasureTheory.ae $μ) (rv%[$μ] $f) (rv%[$μ] $g))
/--
Path of a process with a.e. measurable coordinates is a.e. measurable (product σ-algebra).

Not an `instance`: synthesizing `IsProbabilityMeasure π` via `PSpace` would otherwise loop
through a metavariable process `X`.
-/
theorem PSpace.of_process_path
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {π : Measure Ω} {X : ℕ → Ω → α} (h : ∀ t, PSpace π (X t)) :
    PSpace π (AsPathRV.path X) where
  toIsProbabilityMeasure := (h 0).toIsProbabilityMeasure
  aemeasurable := (aemeasurable_pi_iff (μ := π)).2 fun t => (h t).aemeasurable

/-! ### Binder notation `𝔼`

Python-aligned surface form (cf. `Expectation[x ~ D](f, given=…)` in `../py/sympy`):

* brackets = limits (integrated RV(s) before `:`, free RVs after `|`)
* parentheses = body (+ optional `given` after `|`)
* Integrated slot is always `ident,+`: one RV is bare; two or more pack
  right-nested `JointRandomSymbol` (joint law). That is **not** the same as
  nested `𝔼[x: π](𝔼[y: π](…))` (product of marginals) unless independence.
  Process binders `ℕ → Ω → α` are read via `Expectation.asRV` as path RVs
  `Ω → (ℕ → α)` (e.g. `𝔼[s, a, r : M θ](…)`); ordinary RVs stay definitionally themselves.

* **Scalar (integrate out completely):**
  `𝔼[x: π](f x)` → `Expectation.ofRV π (Expectation.asRV x) …`
  `𝔼[x, y: π](f x y)` → `Expectation.ofRV π (JointRandomSymbol (Expectation.asRV x) (Expectation.asRV y)) …`
* **Scalar conditional at a fixed observation:**
  `𝔼[x: π](f x | y = y0)` / `𝔼[x, z: π](f | y = y0)` → `Expectation.condRV …`
  Joint observations: `| (y, z) = (y0, z0)` (any term on the left of `=`), or the `∧`-chain
  `| y = y0 ∧ z = z0 ∧ …` (two or more conjuncts), which conditions on the joint random variable
  `JointRandomSymbol y (JointRandomSymbol z …)` at `(y0, z0, …)`, as in `ℙ[π](… | y = y0 ∧ z = z0)`.
* **Scalar conditional given random argument(s) (no observation) = σ-algebra conditional expectation:**
  `𝔼[x: π](f x | y)` / `𝔼[x, z: π](f | y t, (u, v), w (t + 1))` → `Expectation.condSigma …`
  `= π[fun ω ↦ f (x ω) | MeasurableSpace.comap y inferInstance]` (Mathlib `condExp`; no density, no
  atoms needed; defined up to `π`-a.e. equality, so compare with `=ᵐ[π]`).
  After `|` come arbitrary terms `Ω → _` (not only names) without a top-level `=` (that would be an
  observation): one is used bare, two or more are packed right-nested by `JointRandomSymbol`
  (`y, z, w` ↦ `(y, (z, w))`; write `(y, z), w` for `((y, z), w)`). The conditioners are outside the
  binder scope: in `𝔼[s: π](f (s t) | s t)` the `s t` after `|` is the random variable.
  A binder is turned into `let x := «integ».…` inside the body, so `𝔼[x: π](f x)` reads `f` at the
  *value* of `x`. That rebinding is kept when `x` is not a local (a constant such as `reward`, or a
  name introduced by the notation) and when the body uses a local `x` as that value
  (`𝔼[a: π](f a)`, `∑' t, γ ^ t * r t`). It is skipped when `x` is already a local and the body
  mentions it only as a random variable inside `ℙ` (`ℙ[π](a t = u | s t = x)`): those occurrences
  keep the outer local, so `SinglePSpace` sees `a t : Ω → _` rather than the integrated path value.
* **Random-valued (integrate out, leave other RVs free):**
  `𝔼[x: π | y]((x + y)^2)` / `𝔼[x, z: π | y](…)` → `Expectation.partialRV …`
  Any number of free RVs after `|` in the brackets.
* **Random-valued + fixed observation:**
  `𝔼[x: π | y](… | r = r0)` / joint integrate likewise → `Expectation.partialRV_cond`
  Joint observations: `| (r, s) = (r0, s0)`.
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

open Lean

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
`rebind[i] = false` skips the `let` for that binder (the body keeps the outer local). -/
partial def Expectation.Macro.unpackRest
    (ys : Array Syntax) (nest : Term) (body : Term) (rebind : Array Bool) : MacroM Term := do
  match ys.toList, rebind.toList with
  | [], _ => pure body
  | [y], r :: _ =>
    if r then
      let y : Ident := ⟨y⟩
      `(let $y := $nest; $body)
    else
      pure body
  | y :: rest, r :: rs =>
    let nest2 ← `(Prod.snd $nest)
    let body' ← Expectation.Macro.unpackRest rest.toArray nest2 body rs.toArray
    if r then
      let y : Ident := ⟨y⟩
      `(let $y := Prod.fst $nest; $body')
    else
      pure body'
  | _, [] => Macro.throwError "𝔼 binder unpack: rebind mask shorter than the binder list"

/-- The measure term of an `expectMeasure` slot: `f a b` ↦ the application `f a b`. -/
def Expectation.Macro.measure (π : TSyntax `expectMeasure) : MacroM Term :=
  match π with
  | `(expectMeasure| $f:term $[$args:term]*) =>
    if args.isEmpty then pure f else `($f $args*)
  | _ => Macro.throwUnsupported

/-! ### Binder notation `ℙ`

Syntax sugar for pointwise evaluation of the canonical densities `prob` / `condProb`.

* `ℙ[π](x)` / `ℙ[π](x, y, …)` → `Measure.probRA π (JointRandomSymbol …)`
  (= `fun ω ↦ ℙ[π](x = (x ω) ∧ y = (y ω) ∧ …)`), magenta joint RA
* `ℙ[π](x, y | z = z0)` / `ℙ[π](x | y = y0 ∧ z = z0 ∧ …)` → `Measure.probCond …`
  (= `fun ω ↦ ℙ[π](x = (x ω) ∧ y = (y ω) | z = z0 ∧ …)`), magenta given black
  (commas left of `|`; `∧`-chains of `=` on the right)
* `ℙ[π](x, y | z)` / `ℙ[π](x, y | z, w, …)` → `Measure.probCondRA …`
  (= `fun ω ↦ ℙ[π](x = (x ω) ∧ y = (y ω) | z = (z ω) ∧ …)`), magenta on both sides
  (commas on both sides of `|`)
* `ℙ[π](x = x0)` → `Measure.prob π x x0` (point / black value)
* `ℙ[π](x = x0 ∧ y = y0 ∧ …)` → `Measure.prob π (JointRandomSymbol …) (x0, …)`
* `ℙ[π](x = x0 | y = y0 ∧ …)` → `Measure.condProb π (JointRandomSymbol x …) (x0, …)`
* `ℙ[π](x = x0 ∧ y = y0 | z = z0)` →
  `Measure.condProb π (JointRandomSymbol (JointRandomSymbol x y) z) ((x0, y0), z0)`
* Both sides of `|` accept any nonempty `∧`-chain of fixed observations.
* `ℙ[π](x = x0 | y)` → `Measure.condProbRA π (x, y) x0`
  (= `fun ω ↦ Measure.condProb π (x, y) (x0, y ω)`), a random expression in `y`.
  Several RAs: `ℙ[π](x = x0 | y, z, …)`; joint left: `ℙ[π](x = x0 ∧ w = w0 | y)`.

Read `=` as “evaluated at” (like `x ↦ x0`), not as an event `{ω | x ω = x0}`.
`∧` packs a joint point; `|` is conditioning (fixed `=` or random arguments).
-/

/-- Right-nested `JointRandomSymbol` chain: `#[x,y,z]` ↦ `JointRandomSymbol x (JointRandomSymbol y z)`. -/
partial def Probability.Macro.mkJointRV (ts : Array Syntax) : MacroM Term := do
  match ts.toList with
  | [] => Macro.throwError "ℙ[π](…) requires at least one factor"
  | [t] => pure ⟨t⟩
  | t :: rest =>
    let t : Term := ⟨t⟩
    let tail ← Probability.Macro.mkJointRV rest.toArray
    `(JointRandomSymbol $t $tail)

/-- Right-nested product of values: `#[a,b,c]` ↦ `(a, (b, c))`. -/
partial def Probability.Macro.mkProd (ts : Array Syntax) : MacroM Term := do
  match ts.toList with
  | [] => Macro.throwError "ℙ[π](…) requires at least one factor"
  | [t] => pure ⟨t⟩
  | t :: rest =>
    let t : Term := ⟨t⟩
    let tail ← Probability.Macro.mkProd rest.toArray
    `(($t, $tail))

syntax:max "ℙ[" term "]" "(" ident,+ ")" : term
syntax:max "ℙ[" term "]" "(" ident,+ "|" ident,+ ")" : term
syntax:max "ℙ[" term "]" "(" ident,+ "|" sepBy1(term:max "=" term:lead, "∧") ")" : term
syntax:max "ℙ[" term "]" "(" sepBy1(term:max "=" term:lead, "∧") ")" : term
syntax:max "ℙ[" term "]" "(" sepBy1(term:max "=" term:lead, "∧") "|" sepBy1(term:max "=" term:lead, "∧") ")" : term
syntax:max "ℙ[" term "]" "(" sepBy1(term:max "=" term:lead, "∧") "|" ident,+ ")" : term

macro_rules
  | `(ℙ[$π]($xs:ident,*)) => do
      let x ← Probability.Macro.mkJointRV xs
      `(Measure.probRA $π $x)
  | `(ℙ[$π]($xs:ident,* | $ys:ident,*)) => do
      let x ← Probability.Macro.mkJointRV xs
      let y ← Probability.Macro.mkJointRV ys
      `(Measure.probCondRA $π (JointRandomSymbol $x $y))
  | `(ℙ[$π]($xs:ident,* | $[$y:term = $y0:term]∧*)) => do
      let x ← Probability.Macro.mkJointRV xs
      let y ← Probability.Macro.mkJointRV y
      let y0 ← Probability.Macro.mkProd y0
      `(Measure.probCond $π (JointRandomSymbol $x $y) $y0)
  | `(ℙ[$π]($[$x:term = $x0:term]∧*)) => do
      let x ← Probability.Macro.mkJointRV x
      let x0 ← Probability.Macro.mkProd x0
      `(Measure.prob $π $x $x0)
  | `(ℙ[$π]($[$x:term = $x0:term]∧* | $[$y:term = $y0:term]∧*)) => do
      let x ← Probability.Macro.mkJointRV x
      let x0 ← Probability.Macro.mkProd x0
      let y ← Probability.Macro.mkJointRV y
      let y0 ← Probability.Macro.mkProd y0
      `(Measure.condProb $π (JointRandomSymbol $x $y) ($x0, $y0))
  | `(ℙ[$π]($[$x:term = $x0:term]∧* | $ys:ident,*)) => do
      let x ← Probability.Macro.mkJointRV x
      let x0 ← Probability.Macro.mkProd x0
      let y ← Probability.Macro.mkJointRV ys
      `(Measure.condProbRA $π (JointRandomSymbol $x $y) $x0)

/-- `true` when `name` occurs in `stx` as an integrated *value* (anything that is not a
random-variable slot of a `ℙ`). Random-variable slots are the bare idents of `ℙ[π](x, y)` and the
left-hand side of each `=` (`ℙ[π](a t = u | s t = x)`). -/
private partial def Expectation.Macro.bodyValueUse
    (stx : Syntax) (name : Name) (inRV : Bool := false) : MacroM Bool := do
  let rec over (stxs : Array Syntax) (rv : Bool) : MacroM Bool :=
    stxs.foldlM (init := false) fun acc s => return acc || (← bodyValueUse s name rv)
  match stx with
  | `(ℙ[$_]($xs:ident,*)) => over xs (rv := true)
  | `(ℙ[$_]($xs:ident,* | $ys:ident,*)) =>
      return (← over xs true) || (← over ys true)
  | `(ℙ[$_]($xs:ident,* | $[$y:term = $y0:term]∧*)) =>
      return (← over xs true) || (← over y true) || (← over y0 false)
  | `(ℙ[$_]($[$x:term = $x0:term]∧* | $[$y:term = $y0:term]∧*)) =>
      return (← over x true) || (← over x0 false) || (← over y true) || (← over y0 false)
  | `(ℙ[$_]($[$x:term = $x0:term]∧* | $ys:ident,*)) =>
      return (← over x true) || (← over x0 false) || (← over ys true)
  | `(ℙ[$_]($[$x:term = $x0:term]∧*)) =>
      return (← over x true) || (← over x0 false)
  | _ =>
      if stx.isIdent then
        return !inRV && stx.getId == name
      else
        over stx.getArgs inRV

open Lean.Elab.Term in
/-- Rebind a binder unless it is already a local whose body occurrences are all `ℙ` random-variable
slots (those must keep seeing the outer local). -/
private def Expectation.Macro.rebindMask (xs : Array Syntax) (body : Syntax) : TermElabM (Array Bool) :=
  xs.mapM fun x => do
    let inScope := (← getLCtx).findFromUserName? x.getId |>.isSome
    if !inScope then
      return true
    else
      Lean.Elab.liftMacroM <| Expectation.Macro.bodyValueUse body x.getId


open Lean.Elab.Term in
/-- Elaborate one `𝔼` form. `build` receives the unpacked body. -/
private def Expectation.Macro.elabExpect (xs : Array Syntax) (body : Syntax)
    (build : Term → MacroM Term) : TermElabM Lean.Expr := do
  let mask ← Expectation.Macro.rebindMask xs body
  let nest := mkIdent `«integ»
  let unpacked ← Lean.Elab.liftMacroM <| Expectation.Macro.unpackRest xs nest ⟨body⟩ mask
  let lam ← if mask.any id then
      `(fun $nest ↦ $unpacked)
    else
      `(fun _ ↦ $unpacked)
  Lean.Elab.Term.elabTerm (← Lean.Elab.liftMacroM <| build lam) none

elab_rules : term
  | `(𝔼[$xs:ident,* : $π]($body)) => do
      let xs := xs.getElems
      let joint ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      Expectation.Macro.elabExpect xs body fun lam => `(Expectation.ofRV $π $joint $lam)
  | `(𝔼[$xs:ident,* : $π]($body | $y:term = $y0)) => do
      let xs := xs.getElems
      let joint ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      Expectation.Macro.elabExpect xs body fun lam => `(Expectation.condEvent $π $joint $y $lam $y0)
  | `(𝔼[$xs:ident,* : $π]($body | $y:term = $y0:term ∧ $[$ys:term = $ys0:term]∧*)) => do
      let xs := xs.getElems
      -- `y = y0 ∧ z = z0 ∧ …` ↦ `JointRandomSymbol y (JointRandomSymbol z …)` at `(y0, z0, …)`
      let conds := #[y] ++ ys
      let vals := #[y0] ++ ys0
      let mut cond : Term := conds.back!
      let mut val : Term := vals.back!
      for i in (List.range (conds.size - 1)).reverse do
        cond ← `(JointRandomSymbol $(conds[i]!) $cond)
        val ← `(($(vals[i]!), $val))
      let joint ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      Expectation.Macro.elabExpect xs body fun lam => `(Expectation.condEvent $π $joint $cond $lam $val)
  | `(𝔼[$xs:ident,* : $π]($body | $ys,*)) => do
      let xs := xs.getElems
      let joint ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      let cond ← Lean.Elab.liftMacroM <| Expectation.Macro.mkJointTerms ys.getElems
      Expectation.Macro.elabExpect xs body fun lam => `(Expectation.condSigma $π $joint $cond $lam)
  | `(𝔼[$xs:ident,* : $π:expectMeasure | $ys,*]($body | $r:term = $r0)) => do
      let π ← Lean.Elab.liftMacroM <| Expectation.Macro.measure π
      let xs := xs.getElems
      let ys := ys.getElems
      let maskX ← Expectation.Macro.rebindMask xs body
      let maskY ← Expectation.Macro.rebindMask ys body
      let integ ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      let free ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint ys
      let nestX := mkIdent `«integ»
      let nestY := mkIdent `«rest»
      let bodyY ← Lean.Elab.liftMacroM <| Expectation.Macro.unpackRest ys nestY body maskY
      let bodyXY ← Lean.Elab.liftMacroM <| Expectation.Macro.unpackRest xs nestX bodyY maskX
      let lam ← if maskX.any id then
          if maskY.any id then `(fun $nestX $nestY ↦ $bodyXY) else `(fun $nestX _ ↦ $bodyXY)
        else
          if maskY.any id then `(fun _ $nestY ↦ $bodyXY) else `(fun _ _ ↦ $bodyXY)
      Lean.Elab.Term.elabTerm (← `(Expectation.partialRV_cond $π $integ $free $r $lam $r0)) none
  | `(𝔼[$xs:ident,* : $π:expectMeasure | $ys,*]($body)) => do
      let π ← Lean.Elab.liftMacroM <| Expectation.Macro.measure π
      let xs := xs.getElems
      let ys := ys.getElems
      let maskX ← Expectation.Macro.rebindMask xs body
      let maskY ← Expectation.Macro.rebindMask ys body
      let integ ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint xs
      let free ← Lean.Elab.liftMacroM <| Expectation.Macro.mkRestJoint ys
      let nestX := mkIdent `«integ»
      let nestY := mkIdent `«rest»
      let bodyY ← Lean.Elab.liftMacroM <| Expectation.Macro.unpackRest ys nestY body maskY
      let bodyXY ← Lean.Elab.liftMacroM <| Expectation.Macro.unpackRest xs nestX bodyY maskX
      let lam ← if maskX.any id then
          if maskY.any id then `(fun $nestX $nestY ↦ $bodyXY) else `(fun $nestX _ ↦ $bodyXY)
        else
          if maskY.any id then `(fun _ $nestY ↦ $bodyXY) else `(fun _ _ ↦ $bodyXY)
      Lean.Elab.Term.elabTerm (← `(Expectation.partialRV $π $integ $free $lam)) none


