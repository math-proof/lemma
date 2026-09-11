import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.MeasurableSpace.Constructions


open MeasureTheory


/--
Canonical reference measure on a measurable space (e.g. Lebesgue on `ℝ`).

Extends `MeasurableSpace`, so `[ReferenceMeasure α]` also provides `[MeasurableSpace α]`.

This is the ambient measure that densities are taken with respect to — analogous to
how sympy treats continuous spaces without naming the measure explicitly.
Unlike a bare `∃ μ, SigmaFinite μ`, this **chooses** a specific measure.
-/
class ReferenceMeasure (α : Type*) extends MeasurableSpace α where
  /-- The reference measure. -/
  measure : Measure α
  /-- Reference measures are required to be σ-finite (so Radon–Nikodym applies). -/
  toSigmaFinite : SigmaFinite measure

attribute [instance] ReferenceMeasure.toSigmaFinite

/-- Explicit accessor (avoids `ReferenceMeasure.measure α` being read as measure-evaluation). -/
abbrev Probability.measure (α : Type*) [ReferenceMeasure α] : Measure α :=
  ReferenceMeasure.measure

/-- Build a `ReferenceMeasure` from an explicit σ-finite measure. -/
@[instance_reducible]
def ReferenceMeasure.of {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] : ReferenceMeasure α where
  toMeasurableSpace := inferInstance
  measure := μ
  toSigmaFinite := inferInstance


/--
[sympy.Probability](https://github.com/sympy/sympy/blob/master/sympy/stats/symbolic_probability.py)

The joint distribution of the random variables `x` and `y` admits a probability
density function — `Pr(x, y)` in sympy notation — w.r.t. the product of the
canonical reference measures on `α` and `β`:
there exists a measurable `p` such that the joint law
(the pushforward of `ℙ` along `ω ↦ (x ω, y ω)`) equals
`((Probability.measure α).prod (Probability.measure β)).withDensity p`.

Also packages that `ℙ` is a probability measure (so `[IsProbabilityMeasure ℙ]` need not
be stated separately once a `Probability` instance is in scope).

The density itself is not a separate hypothesis; it is recovered as
`(Measure.map (fun ω ↦ (x ω, y ω)) ℙ).rnDeriv ((Probability.measure α).prod (Probability.measure β))`
(a.e.).
-/
class Probability
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    (x : Ω → α) (y : Ω → β)
    (ℙ : Measure Ω) :
    Prop where
  /-- `ℙ` is a probability measure on `Ω`. -/
  toIsProbabilityMeasure : IsProbabilityMeasure ℙ
  /-- there exists a joint density `Pr(x, y)` -/
  exists_density :
    ∃ p : α × β → ENNReal, Measurable p ∧
      Measure.map (fun ω ↦ (x ω, y ω)) ℙ =
        ((Probability.measure α).prod (Probability.measure β)).withDensity p

attribute [instance] Probability.toIsProbabilityMeasure


/--
Canonical joint density `Pr(x, y)` (Radon–Nikodym derivative of the joint law).
Equal a.e. to any witnessing density from `exists_density`.
-/
noncomputable def Probability.density
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    (x : Ω → α) (y : Ω → β)
    (ℙ : Measure Ω)
    [Probability x y ℙ] :
    α × β → ENNReal :=
  (Measure.map (fun ω ↦ (x ω, y ω)) ℙ).rnDeriv ((Probability.measure α).prod (Probability.measure β))


/--
Build the `Probability` instance from an explicit density `p`,
its measurability, and the joint-law equation w.r.t. the reference measures, e.g.
`have hP : Probability x y ℙ := Probability.of_density hp hjoint`.
-/
theorem Probability.of_density
    {Ω α β : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α] [ReferenceMeasure β]
    {x : Ω → α} {y : Ω → β}
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    {p : α × β → ENNReal}
    (hp : Measurable p)
    (hjoint : Measure.map (fun ω ↦ (x ω, y ω)) ℙ =
      ((Probability.measure α).prod (Probability.measure β)).withDensity p) :
    Probability x y ℙ where
  toIsProbabilityMeasure := inferInstance
  exists_density := ⟨p, hp, hjoint⟩
