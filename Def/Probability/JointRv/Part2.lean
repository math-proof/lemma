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
import Instance.Probability.JointRv
open MeasureTheory
open scoped ProbabilityTheory


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

