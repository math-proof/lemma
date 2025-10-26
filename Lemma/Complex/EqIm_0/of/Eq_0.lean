import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {z : ℂ}
-- given
  (h : z = 0) :
-- imply
  im z = 0 := by
-- proof
  rw [h]
  simp


-- created on 2025-01-17
