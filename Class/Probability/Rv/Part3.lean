import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Lemma.Measure.Count.eq.ProdCountS
import Class.Probability.Rv.Part2
import Instance.Probability.Rv.Part2
open MeasureTheory


attribute [instance] ReferenceMeasure.toSigmaFinite

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
