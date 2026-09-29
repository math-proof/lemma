import sympy.functions.elementary.complexes
import sympy.Basic
open Real


@[main]
private lemma main
  {x y : ℂ}
-- given
  (h : x = y) :
-- imply
  re x = re y := by
-- proof
  rw [h]


-- created on 2026-09-27
