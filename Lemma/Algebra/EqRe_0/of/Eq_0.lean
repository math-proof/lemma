import sympy.functions.elementary.complexes
import Lemma.Basic


@[main]
private lemma main
  {z : ℂ}
-- given
  (h : z = 0) :
-- imply
  re z = 0 := by
-- proof
  rw [h]
  simp


-- created on 2025-01-17
