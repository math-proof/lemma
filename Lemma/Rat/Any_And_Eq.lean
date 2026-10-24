import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_3
open scoped Pointwise


/--
[coset_intersects_unit_interval](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_3.lean)
-/
@[path]
private lemma main
  {c : RealModRat} :
-- imply
  ∃ x : ℝ, x ∈ Set.Icc 0 1 ∧ QuotientAddGroup.mk (s := Rat.addSubgroup) x = c :=
-- proof
  coset_intersects_unit_interval c


-- created on 2026-10-22
