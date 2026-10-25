/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/MeasureTheory/Measure/VitaliNonmeasurable.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Instance.MeasureTheory.Measure.VitaliNonmeasurable.Part2
import Lemma.Measure.VitaliNonmeasurable
open MeasureTheory


example : ∃ s : Set ℝ, ¬ NullMeasurableSet s (volume : Measure ℝ) :=
  MeasureTheory.vitali_nonmeasurable

