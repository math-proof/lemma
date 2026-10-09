import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {x y : ℂ}
-- given
  (h : x = y) :
-- imply
  im x = im y := by
-- proof
  rw [h]


-- created on 2022-07-02
