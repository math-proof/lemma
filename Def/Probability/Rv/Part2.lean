import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Lemma.Measure.Count.eq.ProdCountS
import Structure.Probability.Rv
open MeasureTheory


attribute [instance] ReferenceMeasure.toSigmaFinite

attribute [simp] CountableMeasure.measure_eq_count


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

