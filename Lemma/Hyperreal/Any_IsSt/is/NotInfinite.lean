import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  (∃ r : ℝ, x.IsSt r) ↔ ¬x.Infinite :=
-- proof
  Hyperreal.exists_st_iff_not_infinite


-- created on 2025-12-18
