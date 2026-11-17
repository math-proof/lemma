module

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public section

open MeasureTheory


/--
Canonical state measure on a measurable space (e.g. Lebesgue on `ℝ`).

Extends `MeasurableSpace`, so `[ReferenceMeasure α]` also provides `[MeasurableSpace α]`.

This is the ambient measure that densities are taken with respect to — analogous to
how sympy treats continuous spaces without naming the measure explicitly.
Unlike a bare `∃ μ, SigmaFinite μ`, this **chooses** a specific measure.
-/
class ReferenceMeasure (α : Type*) extends MeasurableSpace α where
  /-- The state measure. -/
  measure : Measure α
  /-- State measures are required to be σ-finite (so Radon–Nikodym applies). -/
  toSigmaFinite : SigmaFinite measure


attribute [instance] ReferenceMeasure.toSigmaFinite


/--
The ambient `ReferenceMeasure` on `α` is the counting measure.

Extends `ReferenceMeasure`, so `[CountableMeasure α]` also provides `[ReferenceMeasure α]`
(and thus `[MeasurableSpace α]`). Use this instead of repeating
`(h : ReferenceMeasure.measure = Measure.count)` on every lemma.
Typical GradExpect / discrete-HMM binders become
`[CountableMeasure S] [CountableMeasure A]` — no separate `ReferenceMeasure` binder.

Do **not** invent a global instance for every `[Countable α]`: the reference measure is a
chosen ambient, and may be Lebesgue (or other) even on a countable type. Provide
`[CountableMeasure α]` at the lemma / model boundary, or build from an existing
`ReferenceMeasure` with `measure_eq_count := h` when `h : measure = Measure.count`
(e.g. after `ReferenceMeasure.of Measure.count`).
-/
class CountableMeasure (α : Type*) extends ReferenceMeasure α where
  /-- The chosen reference measure equals `Measure.count`. -/
  measure_eq_count : measure = Measure.count


/--
[sympy.PSpace](https://github.com/sympy/sympy/blob/master/sympy/stats/rv.py)

The probability space of a random variable `x : Ω → α`: `π` is a probability measure and
`x` is (almost everywhere) measurable, so its law `π.map x` is a probability measure on `α`.
No density is required — `α` only needs a `MeasurableSpace` (no `ReferenceMeasure`).
This is enough for unconditional expectations `𝔼[x: π](f x)`.
-/
class PSpace
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace α]
    (π : Measure Ω)
    (x : Ω → α) :
    Prop extends IsProbabilityMeasure π where
  aemeasurable : AEMeasurable x π


/--
[sympy.SinglePSpace](https://github.com/sympy/sympy/blob/master/sympy/stats/rv.py)

The probability space of a single random variable `x` whose distribution admits a
probability density function with respect to the reference measure `ReferenceMeasure α`.
Extends `PSpace`, so `[SinglePSpace π x]` also provides `[PSpace π x]` (probability measure +
a.e. measurability). Required by the density based notions `π.prob`, `π.condProb`, `ℙ[π](…)`
and the conditional expectations.
-/
class SinglePSpace
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (π : Measure Ω)
    (x : Ω → α) :
    Prop extends PSpace π x where
  exists_distribution :
    ∃ ρ : α → ENNReal,
      Measurable ρ ∧ π.map x = ReferenceMeasure.measure.withDensity ρ
