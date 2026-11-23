/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/MeasureTheory/Measure/VitaliNonmeasurable.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/
module

public import Instance.MeasureTheory.Measure.VitaliNonmeasurable.Part2
public import Theorem.Measure.VitaliNonmeasurable
open MeasureTheory

public section

example : ∃ s : Set ℝ, ¬ NullMeasurableSet s (volume : Measure ℝ) :=
  MeasureTheory.vitali_nonmeasurable

