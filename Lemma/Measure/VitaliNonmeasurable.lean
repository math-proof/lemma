import Mathlib
import sympy.Basic
import sympy.atlas.MeasureTheory.Measure.VitaliNonmeasurable
open MeasureTheory


/--
[vitali_nonmeasurable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/VitaliNonmeasurable.lean)
-/
@[path]
private lemma vitali_nonmeasurable_eq
  :
-- imply
  ∃ s : Set ℝ, ¬ NullMeasurableSet s (volume : Measure ℝ) := by
-- proof
  apply MeasureTheory.vitali_nonmeasurable


-- created on 2026-10-20
