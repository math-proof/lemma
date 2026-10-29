import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.HasLaw
import Lemma.Measure.Count.eq.ProdCountS
import Structure.Probability.Rv
open MeasureTheory ProbabilityTheory


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
Density-free law: `Distributed X μ π` means `X` has law `μ` under `π`.
Definitionally `HasLaw X μ π` (a.e. measurability + `π.map X = μ`).
-/
abbrev Distributed
    {Ω α : Type*}
    [MeasurableSpace Ω]
    [MeasurableSpace α]
    (X : Ω → α) (μ : Measure α) (π : Measure Ω) : Prop :=
  HasLaw X μ π
