import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x y : ℂ}
-- given
  (h : x = y) :
-- imply
  (starRingEnd ℂ) x = (starRingEnd ℂ) y := by
-- proof
  rw [h]


-- created on 2018-08-18
-- updated on 2026-08-20
