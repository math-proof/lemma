import sympy.Basic
import Mathlib.Analysis.Real.Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x ≥ 0) :
-- imply
  x.st ≥ 0 := by
-- proof
  unfold Hyperreal.st
  split_ifs with h_r
  .
    exact (Hyperreal.isSt_refl_real 0).le (Classical.choose_spec h_r) h
  .
    simp


-- created on 2025-12-11
