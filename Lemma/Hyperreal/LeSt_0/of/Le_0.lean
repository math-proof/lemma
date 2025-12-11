import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x ≤ 0) :
-- imply
  x.st ≤ 0 := by
-- proof
  unfold Hyperreal.st
  split_ifs with h_r
  ·
    exact (Classical.choose_spec h_r).le (Hyperreal.isSt_refl_real 0) h
  ·
    simp


-- created on 2025-12-11
