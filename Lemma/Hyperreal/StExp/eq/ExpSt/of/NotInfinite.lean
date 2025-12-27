import Lemma.Hyperreal.IsSt_St.of.NotInfinite
import sympy.functions.elementary.exponential
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬x.Infinite) :
-- imply
  x.exp.st = x.st.exp := by
-- proof
  have h_st := IsSt_St.of.NotInfinite h
  have h_map := h_st.map Real.continuous_exp.continuousAt
  exact h_map.st_eq


-- created on 2025-12-27
