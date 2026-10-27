import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Lemma.Measure.Count.eq.ProdCountS
import Instance.Probability.Rv.Part2
open MeasureTheory


attribute [instance] ReferenceMeasure.toSigmaFinite

attribute [simp] CountableMeasure.measure_eq_count


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


