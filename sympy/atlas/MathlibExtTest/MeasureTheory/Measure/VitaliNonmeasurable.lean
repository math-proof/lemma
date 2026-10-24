/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/MeasureTheory/Measure/VitaliNonmeasurable.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import sympy.atlas.MeasureTheory.Measure.VitaliNonmeasurable
import Lemma.Measure.VitaliNonmeasurable

open MeasureTheory

example : ∃ s : Set ℝ, ¬ NullMeasurableSet s (volume : Measure ℝ) :=
  MeasureTheory.vitali_nonmeasurable
