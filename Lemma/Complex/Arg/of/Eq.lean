import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x y : ℂ}
-- given
  (h : x = y) :
-- imply
  arg x = arg y := by
-- proof
  rw [h]


-- created on 2018-06-03
