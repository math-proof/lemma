import Lemma.Hyperreal.UFn.of.All_Ufn
import sympy.polys.polyroots
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : x ≥ 0) :
-- imply
  (√x)² = x := by
-- proof
  revert h
  apply UFn.of.All_Ufn x
  intro x h
  simp [Root.sqrt]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [h] with n h
  exact Real.sq_sqrt h


-- created on 2025-12-10
