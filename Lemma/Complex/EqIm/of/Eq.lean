import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x y : ℂ}
-- given
  (h : x = y) :
-- imply
  im x = im y := by
-- proof
  rw [h]


-- created on 2026-09-27
