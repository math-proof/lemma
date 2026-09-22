import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import sympy.stats.symbolic_probability
open MeasureTheory
open scoped ProbabilityTheory

/-- CondIndepFun sugar. Precedence 100 beats Mathlib’s `x ⟂ᵢ[π] y` (50) so the
trailing `| z` is not left behind. `‹Measurable Z›` picks up a local `hz`. -/
notation:100 X:100 " ⟂ᵢ[" μ "] " Y:100 " | " Z:100 =>
  ProbabilityTheory.CondIndepFun
    (MeasurableSpace.comap Z inferInstance)
    (Measurable.comap_le ‹Measurable Z›)
    X Y μ


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
also supplies `PSpace π (x, y)`.
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
Build a joint `PSpace π (x, y)` from an explicit density `p` of the joint law: if
`π.map (x, y)` equals the product reference measure with density `p`, then `(x, y)` admits
`p` as its distribution. The a.e. measurability of the pair is supplied directly.
-/
theorem JointRandomSymbol.of_density
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    {π : Measure Ω}
    {x : Ω → α} {y : Ω → β} [IsProbabilityMeasure π]
    {p : α × β → ENNReal}
    (hxy : AEMeasurable (x, y) π)
    (hp : Measurable p)
    (hjoint : π.map (x, y) =
      (ReferenceMeasure.measure.prod ReferenceMeasure.measure).withDensity p) :
    PSpace π (x, y) :=
  { toIsProbabilityMeasure := inferInstance
    aemeasurable := hxy
    exists_distribution := ⟨p, ⟨hp⟩, hjoint⟩ }


/--
Two random variables whose laws each admit a density (`PSpace π x` and
`PSpace π y`) also span a **joint** probability space with density when they are
independent: by `IndepFun`, the joint law is the product of the marginal laws, and the
product of two measures with densities `px`, `py` is the product measure with density
`fun z ↦ px z.1 * py z.2`. The a.e. measurability of `x` and `y` needed by `IndepFun` is
read off the `PSpace` instances (which package `AEMeasurable`); plain `Measurable`
hypotheses are not required. The converse is false without independence — two ac
marginals can have a singular joint law (e.g. `y = x` over a Lebesgue state space).
-/
theorem JointRandomSymbol.of_indep
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    {π : Measure Ω}
    {x : Ω → α} {y : Ω → β}
    [PSpace π x] [PSpace π y]
    (hxy : ProbabilityTheory.IndepFun x y π) :
    PSpace π (x, y) := by
  let μ : Measure α := ReferenceMeasure.measure
  let ν : Measure β := ReferenceMeasure.measure
  let px := π.prob x
  let py := π.prob y
  let p : α × β → ENNReal := fun z ↦ px z.1 * py z.2
  have hpx : Measurable px := Measure.measurable_rnDeriv _ _
  have hpy : Measurable py := Measure.measurable_rnDeriv _ _
  have hp : Measurable p :=
    (hpx.comp measurable_fst).mul (hpy.comp measurable_snd)
  have haex : AEMeasurable x π := PSpace.aemeasurable
  have haey : AEMeasurable y π := PSpace.aemeasurable
  have hindep : π.map (x, y) = (π.map x).prod (π.map y) :=
    ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map haex haey hxy
  have hjoint : π.map (x, y) = (μ.prod ν).withDensity p := by
    rw [hindep, PSpace.map_eq_withDensity_density,
      PSpace.map_eq_withDensity_density, prod_withDensity hpx hpy]
  exact JointRandomSymbol.of_density (haex.prodMk haey) hp hjoint

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
    [ReferenceMeasure α]
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
    [PSpace π (x, y)]
    (f : α → β)
    (y0 : γ) :
    β :=
  expectation
    (ReferenceMeasure.measure.withDensity fun a ↦
      π.condProb (x, y) (a, y0))
    f

/--
Conditional expectation of an ordinary observable of `x` given the random argument `y`
(no fixed observation). “Random argument” (RA) is distinct from a free random variable. For each outcome `ω`:

  `(Expectation.condRA π x y f) ω = Expectation.condRV π x y f (y ω)`

So the result is still random (`Ω → β`): a random expression in the random
argument `y` (or a joint of several). Binder forms: `𝔼[x: π](f x | y)` and
`𝔼[x: π](f x | y, z, …)`. Names after `|` only condition — not free in the body
(contrast `𝔼[x: π | y](…)` / `partialRV`).
-/
noncomputable def Expectation.condRA
    {Ω α γ β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ]
    [Expectation β]
    (π : Measure Ω)
    (x : Ω → α) (y : Ω → γ)
    [PSpace π (x, y)]
    (f : α → β) :
    Ω → β :=
  fun ω ↦ Expectation.condRV π x y f (y ω)

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
    [PSpace π (x, y)]
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
    [PSpace π (x, y, r)]
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

Binder form: `𝔼[x: π | y, z](body | r, s)`.
-/
noncomputable def Expectation.partialRV_RA
    {Ω α γ ρ β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ] [ReferenceMeasure ρ]
    [Expectation β]
    (π : Measure Ω)
    (x : Ω → α) (y : Ω → γ) (r : Ω → ρ)
    [PSpace π (x, y, r)]
    (f : α → γ → β) :
    Ω → β :=
  fun ω ↦ Expectation.partialRV_cond π x y r f (r ω) ω

/-! ### Binder notation `𝔼`

Python-aligned surface form (cf. `Expectation[x ~ D](f, given=…)` in `../py/sympy`):

* brackets = limits (integrated RV(s) before `:`, free RVs after `|`)
* parentheses = body (+ optional `given` after `|`)
* Integrated slot is always `ident,+`: one RV is bare; two or more pack
  right-nested `JointRandomSymbol` (joint law). That is **not** the same as
  nested `𝔼[x: π](𝔼[y: π](…))` (product of marginals) unless independence.

* **Scalar (integrate out completely):**
  `𝔼[x: π](f x)` → `Expectation.ofRV π x …`
  `𝔼[x, y: π](f x y)` → `Expectation.ofRV π (JointRandomSymbol x y) …`
* **Scalar conditional at a fixed observation:**
  `𝔼[x: π](f x | y = y0)` / `𝔼[x, z: π](f | y = y0)` → `Expectation.condRV …`
  Joint observations: `| (y, z) = (y0, z0)` (any term on the left of `=`).
* **Scalar conditional given random argument(s) (no observation):**
  `𝔼[x: π](f x | y)` / `𝔼[x, z: π](f | y, w)` → `Expectation.condRA …`
  Result is `Ω → β` (random in the RA); names after `|` in the parens condition only.
* **Random-valued (integrate out, leave other RVs free):**
  `𝔼[x: π | y]((x + y)^2)` / `𝔼[x, z: π | y](…)` → `Expectation.partialRV …`
  Any number of free RVs after `|` in the brackets.
* **Random-valued + fixed observation:**
  `𝔼[x: π | y](… | r = r0)` / joint integrate likewise → `Expectation.partialRV_cond`
  Joint observations: `| (r, s) = (r0, s0)`.
* **Random-valued + random argument(s) (no observation):**
  `𝔼[x: π | y](body | r, s)` / joint integrate likewise → `Expectation.partialRV_RA`
  Free names in the brackets may appear in the body; trailing `| r, s` only condition.
-/

syntax:max "𝔼[" ident,+ ":" term:max "]" "(" term:51 ")" : term
syntax:max "𝔼[" ident,+ ":" term:max "]" "(" term:51 "|" term:max "=" term:51 ")" : term
syntax:max "𝔼[" ident,+ ":" term:max "]" "(" term:51 "|" ident,+ ")" : term
syntax:max "𝔼[" ident,+ ":" term:max "|" ident,+ "]" "(" term:51 ")" : term
syntax:max "𝔼[" ident,+ ":" term:max "|" ident,+ "]" "(" term:51 "|" term:max "=" term:51 ")" : term
syntax:max "𝔼[" ident,+ ":" term:max "|" ident,+ "]" "(" term:51 "|" ident,+ ")" : term

open Lean

/-- Right-nested `JointRandomSymbol` chain: `#[x,y,z]` ↦ `JointRandomSymbol x (JointRandomSymbol y z)`.
One element returns that ident bare. -/
partial def Expectation.Macro.mkRestJoint (ys : Array Syntax) : MacroM Term := do
  match ys.toList with
  | [] => Macro.throwError "𝔼[…](…) requires at least one random variable in this slot"
  | [y] => pure ⟨y⟩
  | y :: rest =>
    let y : Term := ⟨y⟩
    let tail ← Expectation.Macro.mkRestJoint rest.toArray
    `(JointRandomSymbol $y $tail)

/-- Unpack a right-nested product into `let y := nest.1; …; body`. -/
partial def Expectation.Macro.unpackRest
    (ys : Array Syntax) (nest : Term) (body : Term) : MacroM Term := do
  match ys.toList with
  | [] => pure body
  | [y] =>
    let y : Ident := ⟨y⟩
    `(let $y := $nest; $body)
  | y :: rest =>
    let y : Ident := ⟨y⟩
    let nest2 ← `(Prod.snd $nest)
    let body' ← Expectation.Macro.unpackRest rest.toArray nest2 body
    `(let $y := Prod.fst $nest; $body')

macro_rules
  | `(𝔼[$xs:ident,* : $π]($body)) => do
      let xs := xs.getElems
      let joint ← Expectation.Macro.mkRestJoint xs
      let nest := mkIdent `«integ»
      let unpacked ← Expectation.Macro.unpackRest xs nest body
      `(Expectation.ofRV $π $joint (fun $nest ↦ $unpacked))
  | `(𝔼[$xs:ident,* : $π]($body | $y:term = $y0)) => do
      let xs := xs.getElems
      let joint ← Expectation.Macro.mkRestJoint xs
      let nest := mkIdent `«integ»
      let unpacked ← Expectation.Macro.unpackRest xs nest body
      `(Expectation.condRV $π $joint $y (fun $nest ↦ $unpacked) $y0)
  | `(𝔼[$xs:ident,* : $π]($body | $ys,*)) => do
      let xs := xs.getElems
      let ys := ys.getElems
      let joint ← Expectation.Macro.mkRestJoint xs
      let ra ← Expectation.Macro.mkRestJoint ys
      let nest := mkIdent `«integ»
      let unpacked ← Expectation.Macro.unpackRest xs nest body
      `(Expectation.condRA $π $joint $ra (fun $nest ↦ $unpacked))
  | `(𝔼[$xs:ident,* : $π | $ys,*]($body | $r:term = $r0)) => do
      let xs := xs.getElems
      let ys := ys.getElems
      let integ ← Expectation.Macro.mkRestJoint xs
      let free ← Expectation.Macro.mkRestJoint ys
      let nestX := mkIdent `«integ»
      let nestY := mkIdent `«rest»
      let bodyY ← Expectation.Macro.unpackRest ys nestY body
      let bodyXY ← Expectation.Macro.unpackRest xs nestX bodyY
      `(Expectation.partialRV_cond $π $integ $free $r (fun $nestX $nestY ↦ $bodyXY) $r0)
  | `(𝔼[$xs:ident,* : $π | $ys,*]($body | $rs,*)) => do
      let xs := xs.getElems
      let ys := ys.getElems
      let rs := rs.getElems
      let integ ← Expectation.Macro.mkRestJoint xs
      let free ← Expectation.Macro.mkRestJoint ys
      let ra ← Expectation.Macro.mkRestJoint rs
      let nestX := mkIdent `«integ»
      let nestY := mkIdent `«rest»
      let bodyY ← Expectation.Macro.unpackRest ys nestY body
      let bodyXY ← Expectation.Macro.unpackRest xs nestX bodyY
      `(Expectation.partialRV_RA $π $integ $free $ra (fun $nestX $nestY ↦ $bodyXY))
  | `(𝔼[$xs:ident,* : $π | $ys,*]($body)) => do
      let xs := xs.getElems
      let ys := ys.getElems
      let integ ← Expectation.Macro.mkRestJoint xs
      let free ← Expectation.Macro.mkRestJoint ys
      let nestX := mkIdent `«integ»
      let nestY := mkIdent `«rest»
      let bodyY ← Expectation.Macro.unpackRest ys nestY body
      let bodyXY ← Expectation.Macro.unpackRest xs nestX bodyY
      `(Expectation.partialRV $π $integ $free (fun $nestX $nestY ↦ $bodyXY))


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

syntax:max "ℙ[" term:max "]" "(" ident,+ ")" : term
syntax:max "ℙ[" term:max "]" "(" ident,+ "|" ident,+ ")" : term
syntax:max "ℙ[" term:max "]" "(" ident,+ "|" sepBy1(term:max "=" term:lead, "∧") ")" : term
syntax:max "ℙ[" term:max "]" "(" sepBy1(term:max "=" term:lead, "∧") ")" : term
syntax:max "ℙ[" term:max "]" "(" sepBy1(term:max "=" term:lead, "∧") "|" sepBy1(term:max "=" term:lead, "∧") ")" : term
syntax:max "ℙ[" term:max "]" "(" sepBy1(term:max "=" term:lead, "∧") "|" ident,+ ")" : term

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
