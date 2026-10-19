import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
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

/-- Build a `ReferenceMeasure` from an explicit σ-finite measure. -/
@[instance_reducible]
def ReferenceMeasure.of {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] : ReferenceMeasure α where
  toMeasurableSpace := inferInstance
  measure := μ
  toSigmaFinite := inferInstance

/--
The product of two state measure spaces is a state measure space on `α × β`, whose state
measure is the product measure. This lets a joint random variable `(x, y) : Ω → α × β`
follow an ordinary `Distribution π ρ` via `~`, with the product measure as the state measure.
-/
noncomputable instance ReferenceMeasure.prod [ReferenceMeasure α] [ReferenceMeasure β] :
    ReferenceMeasure (α × β) where
  toMeasurableSpace := inferInstance
  measure := ReferenceMeasure.measure.prod ReferenceMeasure.measure
  toSigmaFinite := inferInstance

/-- Counting measure as the state measure on Fin n → α when α is discrete/countable. -/
noncomputable instance {n : ℕ} {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] :
    ReferenceMeasure (Fin n → α) where
  toMeasurableSpace := inferInstance
  measure := (Measure.count : Measure (Fin n → α))
  toSigmaFinite := inferInstance


/--
The ambient `ReferenceMeasure` on `α` is the counting measure.

Extends `ReferenceMeasure`, so `[CountableMeasure α]` also provides `[ReferenceMeasure α]`
(and thus `[MeasurableSpace α]`). Use this instead of repeating
`(h : (ReferenceMeasure.measure : Measure α) = Measure.count)` on every lemma.
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

attribute [simp] CountableMeasure.measure_eq_count

/-- Matches the `ReferenceMeasure (Fin n → α)` instance above (counting measure).
Also provides that `ReferenceMeasure` via `extends`. Construct other instances by
filling the parent fields (or `toReferenceMeasure := …`) plus `measure_eq_count`. -/
noncomputable instance {n : ℕ} {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] :
    CountableMeasure (Fin n → α) where
  measure := (Measure.count : Measure (Fin n → α))
  toSigmaFinite := inferInstance
  measure_eq_count := rfl


/--
[sympy.Distribution](https://github.com/sympy/sympy/blob/master/sympy/stats/rv.py)

`π` is the state / probability measure; `ρ` is the density w.r.t. `ReferenceMeasure`.
-/
structure Distribution
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (π : Measure Ω)
    (ρ : α → ENNReal) where
  measurable_density : Measurable ρ


def Distribution.measure
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {π : Measure Ω} {ρ : α → ENNReal}
    (_ : Distribution π ρ) :
    Measure Ω :=
  π


def Distribution.density
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {π : Measure Ω} {ρ : α → ENNReal}
    (_ : Distribution π ρ) :
    α → ENNReal :=
  ρ


/--
`x ~ D` — binary operator asserting that the random variable `x` follows the distribution
`D : Distribution π ρ`:
`D.measure.map x = ReferenceMeasure.measure.withDensity D.density`.
-/
def Distributed
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {π : Measure Ω} {ρ : α → ENNReal}
    (x : Ω → α)
    (_ : Distribution π ρ) :
    Prop :=
  π.map x = ReferenceMeasure.measure.withDensity ρ

notation:50 x:51 " ~ " D:52 => Distributed x D


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
probability density function with respect to the reference measure `ReferenceMeasure α`
(`x ~ D` for some `D : Distribution π ρ`). Extends `PSpace`, so `[SinglePSpace π x]` also
provides `[PSpace π x]` (probability measure + a.e. measurability). Required by the density
based notions `π.prob`, `π.condProb`, `ℙ[π](…)` and the conditional expectations.
-/
class SinglePSpace
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (π : Measure Ω)
    (x : Ω → α) :
    Prop extends PSpace π x where
  exists_distribution : ∃ (ρ : α → ENNReal) (D : Distribution π ρ), x ~ D
