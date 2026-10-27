import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Lemma.Measure.Count.eq.ProdCountS
import Def.Probability.Rv.Part2
open MeasureTheory


attribute [instance] ReferenceMeasure.toSigmaFinite

attribute [simp] CountableMeasure.measure_eq_count


notation:50 x:51 " ~ " D:52 => Distributed x D


