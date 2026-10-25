import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Abbrev.Analysis.MeasureTheory.Section_1_1_1.Part2
open BoundedInterval


/-- Length is always non-negative -/
lemma BoundedInterval.length_nonneg (I: BoundedInterval) : 0 ≤ I.length := le_max_right _ _

