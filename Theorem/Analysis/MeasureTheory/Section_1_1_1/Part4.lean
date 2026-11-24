module
public import Def.Analysis.MeasureTheory.Notation.Part2
public import Theorem.Analysis.Section_9_1.Part3
public import Instance.Analysis.MeasureTheory.Section_1_1_1.Part3
open BoundedInterval


public section

/-- The intersection of {name}`BoundedInterval`s equals the set-theoretic intersection. -/
@[simp]
theorem BoundedInterval.inter_eq (I J: BoundedInterval) : (I ∩ J : BoundedInterval) = (I:Set ℝ) ∩ (J:Set ℝ)  :=
  (inter I J).choose_spec.symm

