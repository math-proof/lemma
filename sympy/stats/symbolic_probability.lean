import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.EReal.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import sympy.stats.rv
open MeasureTheory


/--
[sympy.PSpace.probability](https://github.com/sympy/sympy/blob/master/sympy/stats/rv.py)

Probability of an event for a single random variable: the usual definition of probability
as a function of a condition. `Probability π x s` is the probability that `x` takes a value
in the event `s : Set α` — the value of the law of `x` (the pushforward of `π` along `x`)
at `s` — and is a non-negative scalar (`ENNReal`, at most `1` since `π` is a probability
measure):

  `Probability π x s = π.map x s`

For a measurable event this equals `π {ω | x ω ∈ s}` (`Measure.map_apply`);
a point condition is written as a set, e.g. `{a}` in the discrete case.
-/
noncomputable def Probability
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (π : Measure Ω)
    (x : Ω → α)
    [SinglePSpace π x]
    (s : Set α) :
    ENNReal :=
  π.map x s


/--
Interface for expectation of `β`-valued observables under a law `ν : Measure α`.

Instances cover the scalar and product codomains used by sympy-style probability:
`ENNReal` (non-neg Lebesgue), `EReal` (signed extended), `ℂ` (Bochner), and
componentwise `List.Vector` / `Tensor` (see `sympy.stats.symbolic_multivariate_probability`).

Call sites use the exported field `expectation ν f` (same pattern as
`class Operate` / `operate`).
-/
class Expectation (β : Type*) where
  /-- Expectation of an observable `f : α → β` under `ν`. -/
  expectation : {α : Type*} → [MeasurableSpace α] → Measure α → (α → β) → β

export Expectation (expectation)

/--
[sympy.Expectation](https://github.com/sympy/sympy/blob/master/sympy/stats/symbolic_probability.py)

Polymorphic expectation via `[Expectation β]`: write `expectation ν f` for
`f : α → β`.

* `β = ENNReal` — Lebesgue integral `∫⁻ a, f a ∂ν` (non-negative; existing lemmas)
* `β = EReal` — signed extended expectation via positive/negative parts
* `β = ℝ` — Bochner integral `∫ a, f a ∂ν` (meaningful when integrable)
* `β = ℂ` — Bochner integral `∫ a, f a ∂ν` (meaningful when integrable)
* complete real normed spaces `E` (e.g. `Θ →L[ℝ] ℝ`) — Bochner integral (low-priority fallback)
* vectors / tensors — componentwise (import `sympy.stats.symbolic_multivariate_probability`)

sympy's `Expectation` carries the distribution in its limits (`Expectation[a:θ](f(a))`
means `a ~ θ`); here the law is the explicit first argument. For a random variable
`x : Ω → α` with state measure `π` the law is the pushforward `π.map x`, so

  `expectation (π.map x) f = …`

Conditioning enters by taking the conditional law — e.g. `expectation
(ReferenceMeasure.measure.withDensity (fun a ↦ π.condProb (x, y) (a, b))) f` is
`𝔼[f(x) | y = b]`.
-/

noncomputable instance : Expectation ENNReal where
  expectation ν f := ∫⁻ a, f a ∂ν

/-- Unfolding rule for the `ENNReal` instance (use `simp only [expectation_ennreal]`). -/
@[simp] theorem expectation_ennreal
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : α → ENNReal) :
    expectation ν f = ∫⁻ a, f a ∂ν :=
  rfl

/--
Signed extended-real expectation: `E f = E f⁺ - E f⁻`, where the positive/negative
parts are the non-negative observables `(fun a ↦ (f a).toENNReal)` and
`(fun a ↦ (-f a).toENNReal)`, integrated with the `ENNReal` instance of
`expectation`. Mathlib's `EReal` arithmetic sends the indeterminate `⊤ - ⊤` to `⊥`.
-/
noncomputable instance : Expectation EReal where
  expectation ν f := expectation ν (fun a ↦ (f a).toENNReal) - expectation ν (fun a ↦ (-f a).toENNReal)

/--
Complex (Bochner) expectation. Equals the classical integral when `f` is integrable;
Mathlib's Bochner integral is `0` when not integrable — treat integrability as a
side condition in theorems that need a meaningful value.
-/
noncomputable instance : Expectation ℂ where
  expectation ν f := ∫ a, f a ∂ν

/--
Real (Bochner) expectation. Equals the classical integral when `f` is integrable;
Mathlib's Bochner integral is `0` when not integrable — treat integrability as a
side condition in theorems that need a meaningful value.
-/
noncomputable instance : Expectation ℝ where
  expectation ν f := ∫ a, f a ∂ν

/-- Unfolding rule for the `ℝ` instance (use `simp only [expectation_real]`). -/
@[simp] theorem expectation_real
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (f : α → ℝ) :
    expectation ν f = ∫ a, f a ∂ν :=
  rfl

/--
Vector-valued (Bochner) expectation for any complete real normed space `E`
(e.g. `Θ →L[ℝ] ℝ` gradients), `expectation ν f = ∫ a, f a ∂ν`. Declared with low priority so
that the dedicated instances (`ℝ`, `ℂ`, and the componentwise `List.Vector` / `Tensor` ones
of `sympy.stats.symbolic_multivariate_probability`) are preferred wherever they apply;
for `ℝ` and `ℂ` it agrees definitionally with them.
-/
noncomputable instance (priority := low) instExpectationBochner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] :
    Expectation E where
  expectation ν f := ∫ a, f a ∂ν

/-- Unfolding rule for the Bochner instance (use `simp only [expectation_bochner]`). -/
@[simp] theorem expectation_bochner
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure α) (f : α → E) :
    expectation ν f = ∫ a, f a ∂ν :=
  rfl

/--
Canonical density `Pr(x)` of a single random variable (Radon–Nikodym derivative of its
law w.r.t. the canonical state measure). Equal a.e. to any witnessing density from
`SinglePSpace.exists_distribution`. Lives in `MeasureTheory.Measure` (alongside `map` and
`rnDeriv`) so it reads in dot form `π.prob x`, next to `π.map x`.
-/
noncomputable def MeasureTheory.Measure.prob
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (π : Measure Ω)
    (x : Ω → α)
    [SinglePSpace π x] :
    α → ENNReal :=
  (π.map x).rnDeriv ReferenceMeasure.measure


/--
Canonical conditional density `Pr(x | y)` of a joint random symbol `(x, y)`: the joint
density `π.prob (x, y)` divided by the marginal density of the second component — the
Bayes formula `Pr(x | y) = Pr(x, y) / Pr(y)`. Lives in `MeasureTheory.Measure` so it
reads in dot form `π.condProb (x, y)`, mirroring `π.prob (x, y)`.
-/
noncomputable def MeasureTheory.Measure.condProb
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    (π : Measure Ω)
    (xy : Ω → α × β)
    [SinglePSpace π xy] :
    α × β → ENNReal :=
  fun z ↦ π.prob xy z /
    (π.map (fun ω ↦ (xy ω).2)).rnDeriv ReferenceMeasure.measure z.2


/--
Density of `x` evaluated at the realized value of `x` (random argument / magenta).
For each outcome `ω`:

  `(Measure.probRA π x) ω = Measure.prob π x (x ω)`

So the result is random (`Ω → ENNReal`). Binder form: `ℙ[π](x)`.
-/
noncomputable def MeasureTheory.Measure.probRA
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (π : Measure Ω)
    (x : Ω → α)
    [SinglePSpace π x] :
    Ω → ENNReal :=
  fun ω ↦ π.prob x (x ω)


/--
Conditional density of the first component of `xy` at its realized value, given a
fixed observation of the second (magenta RA on the left). For each `ω`:

  `(Measure.probCond π xy y0) ω = Measure.condProb π xy ((xy ω).1, y0)`

Binder form: `ℙ[π](x | y = y0)` (joints via the macro).
-/
noncomputable def MeasureTheory.Measure.probCond
    {Ω α γ : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ]
    (π : Measure Ω)
    (xy : Ω → α × γ)
    [SinglePSpace π xy]
    (y0 : γ) :
    Ω → ENNReal :=
  fun ω ↦ π.condProb xy ((xy ω).1, y0)


/--
Conditional density of the first component of `xy` at the realized joint value,
given the realized second component (magenta RA on both sides). For each `ω`:

  `(Measure.probCondRA π xy) ω = Measure.condProb π xy (xy ω)`

Binder form: `ℙ[π](x, y | z)` / `ℙ[π](x, y | z, w, …)`.
-/
noncomputable def MeasureTheory.Measure.probCondRA
    {Ω α γ : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ]
    (π : Measure Ω)
    (xy : Ω → α × γ)
    [SinglePSpace π xy] :
    Ω → ENNReal :=
  fun ω ↦ π.condProb xy (xy ω)


/--
Conditional probability of a point of the first component of a joint `xy`
given its second component as a random argument (no fixed observation).
For each outcome `ω`:

  `(Measure.condProbRA π xy x0) ω = Measure.condProb π xy (x0, (xy ω).2)`

So the result is still random (`Ω → ENNReal`): a random expression in `xy.2`.
Binder form: `ℙ[π](x = x0 | y)` elaborates with `xy = (x, y)`.
-/
noncomputable def MeasureTheory.Measure.condProbRA
    {Ω α γ : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure γ]
    (π : Measure Ω)
    (xy : Ω → α × γ)
    [SinglePSpace π xy]
    (x0 : α) :
    Ω → ENNReal :=
  fun ω ↦ π.condProb xy (x0, (xy ω).2)


/--
The law of `x` equals the state measure with density `π.prob x`: the
distribution in `SinglePSpace.exists_distribution` gives absolute continuity, and the
Radon–Nikodym theorem reconstructs the measure from its canonical derivative.
-/
theorem SinglePSpace.map_eq_withDensity_density
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {π : Measure Ω}
    {x : Ω → α}
    [SinglePSpace π x] :
    π.map x =
      ReferenceMeasure.measure.withDensity (π.prob x) := by
  have hp : SinglePSpace π x := inferInstance
  obtain ⟨ρ, _, hlaw⟩ := hp.exists_distribution
  exact (Measure.withDensity_rnDeriv_eq (π.map x) _
    (hlaw ▸ withDensity_absolutelyContinuous _ _)).symm


/-- An `x ~ D` hypothesis, together with an a.e. measurability proof for `x`, supplies the
`SinglePSpace D.measure x` instance. -/
theorem Distributed.pspace
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {π : Measure Ω} [IsProbabilityMeasure π]
    {x : Ω → α} {ρ : α → ENNReal}
    {D : Distribution π ρ}
    (h : x ~ D)
    (hx : AEMeasurable x π) :
    SinglePSpace π x :=
  { toIsProbabilityMeasure := inferInstance
    aemeasurable := hx
    exists_distribution := ⟨D.density, D, h⟩ }


/--
`x ~ D` is equivalent to the canonical density of `x` being a.e. equal to `D`'s density
(`π.prob x =ᵐ[ReferenceMeasure.measure] ρ`).
-/
theorem Distributed_iff
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {π : Measure Ω}
    {x : Ω → α} {ρ : α → ENNReal}
    [SinglePSpace π x]
    (D : Distribution π ρ) :
    x ~ D ↔ π.prob x =ᵐ[ReferenceMeasure.measure] ρ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h : D.measure.map x =
        ReferenceMeasure.measure.withDensity D.density := h
    show (D.measure.map x).rnDeriv ReferenceMeasure.measure =ᵐ[ReferenceMeasure.measure] D.density
    rw [h]
    exact Measure.rnDeriv_withDensity _ D.measurable_density
  · exact (@SinglePSpace.map_eq_withDensity_density Ω α _ _ π x _).trans
      (withDensity_congr_ae h)
