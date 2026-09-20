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

The probability space of a single random variable `x`, whose distribution admits a
probability density function
-/
class PSpace
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (π : Measure Ω)
    (x : Ω → α) :
    Prop extends IsProbabilityMeasure π where
  aemeasurable : AEMeasurable x π
  exists_distribution : ∃ (ρ : α → ENNReal) (D : Distribution π ρ), x ~ D
