/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/MeasureTheory/Measure/Lebesgue/Empty.Finite.lean -/
module

public import Theorem.Measure.Lebesgue.Finite
open MeasureTheory Set
open scoped ENNReal

public section

example (E : Set ℝ) (hE : volume E < ∞) (X : ℝ) :
    ∃ x : ℝ, X < x ∧ x ∉ E :=
  MeasureTheory.exists_gt_not_mem_of_volume_lt_top E hE X

