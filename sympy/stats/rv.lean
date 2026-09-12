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
follow an ordinary `Distribution 𝕡 π` via `~`, with the product measure as the state measure.
-/
noncomputable instance ReferenceMeasure.prod [ReferenceMeasure α] [ReferenceMeasure β] :
    ReferenceMeasure (α × β) where
  toMeasurableSpace := inferInstance
  measure := ReferenceMeasure.measure.prod ReferenceMeasure.measure
  toSigmaFinite := inferInstance


/--
[sympy Distribution](https://github.com/sympy/sympy/blob/master/sympy/stats/rv.py)

A distribution bundles the ambient probability measure `𝕡` together with a density
`π : α → ENNReal` w.r.t. the canonical state measure on `α`. It is the Lean counterpart
of a py distribution object (e.g. `NormalDistribution(μ, σ²)`) and is the right operand of
the binary operator `~`: given `D : Distribution 𝕡 π`, write `x ~ D`.

The density measurability is bundled, so a `Distributed` hypothesis is self-sufficient and
directly supplies the `PSpace` instance (`Distributed.pspace`).

The packed parameters are recovered C++-style with dot notation: `D.measure` is the ambient
probability measure `𝕡`, `D.density` is the density `π` (both are `rfl` to the parameter).
-/
structure Distribution
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (𝕡 : Measure Ω)
    (π : α → ENNReal) where
  /-- the density `π` is measurable -/
  measurable_density : Measurable π


/-- The ambient probability measure packed in a `Distribution 𝕡 π` (`D.measure`). -/
def Distribution.measure
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {𝕡 : Measure Ω} {π : α → ENNReal}
    (_ : Distribution 𝕡 π) :
    Measure Ω :=
  𝕡


/-- The density packed in a `Distribution 𝕡 π` (`D.density`). -/
def Distribution.density
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {𝕡 : Measure Ω} {π : α → ENNReal}
    (_ : Distribution 𝕡 π) :
    α → ENNReal :=
  π


/--
`x ~ D` — binary operator asserting that the random variable `x` follows the distribution
`D : Distribution 𝕡 π`:
`D.measure.map x = ReferenceMeasure.measure.withDensity D.density`.
This is the Lean counterpart of the py framework's binary condition
`Distributed(x, π)`, rendered `x ~ π`.

Given a measurability proof `hπ : Measurable π`, an anonymous distribution bundle is
written `(⟨hπ⟩ : Distribution 𝕡 π)`.
-/
def Distributed
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    {𝕡 : Measure Ω} {π : α → ENNReal}
    (x : Ω → α)
    (_ : Distribution 𝕡 π) :
    Prop :=
  𝕡.map x = ReferenceMeasure.measure.withDensity π

notation:50 x:51 " ~ " D:52 => Distributed x D


/--
[sympy.SinglePSpace](https://github.com/sympy/sympy/blob/master/sympy/stats/rv.py)

The probability space of a single random variable `x`, whose distribution admits a
probability density function — `Pr(x)` in sympy notation — w.r.t. the canonical state
measure on `α`: there exists a distribution `D : Distribution 𝕡 π` that `x` follows
(`x ~ D`), i.e. the law of `x` (the pushforward of `𝕡` along `x`) equals
`ReferenceMeasure.measure.withDensity π`.

Also packages that `𝕡` is a probability measure (so `[IsProbabilityMeasure 𝕡]` need not
be stated separately once a `PSpace` instance is in scope).

The density itself is not a separate hypothesis; it is recovered as `PSpace.density 𝕡 x`
(a.e., in `sympy.stats.symbolic_probability`). The probability of an event is
`Probability`.
-/
class PSpace
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [ReferenceMeasure α]
    (𝕡 : Measure Ω)
    (x : Ω → α) :
    Prop where
  /-- `𝕡` is a probability measure on `Ω`. -/
  toIsProbabilityMeasure : IsProbabilityMeasure 𝕡
  /-- there exists a distribution `D` (bundling a measurable density) that `x` follows -/
  exists_distribution :
    ∃ (π : α → ENNReal) (D : Distribution 𝕡 π), x ~ D

attribute [instance] PSpace.toIsProbabilityMeasure
