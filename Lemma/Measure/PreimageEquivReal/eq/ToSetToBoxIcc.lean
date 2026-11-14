import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
open BoundedInterval
@[path]
private lemma main
  {a b : ℝ} :
-- imply
  EuclideanSpace'.equiv_Real ⁻¹' Set.Icc a b = (BoundedInterval.Icc a b).toBox.toSet :=
-- proof
  preimage_Icc_eq_box a b


-- created on 2026-10-22
