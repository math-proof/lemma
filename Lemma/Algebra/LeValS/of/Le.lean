import sympy.Basic


@[main]
private lemma main
  {i j : Fin n}
-- given
  (h : i ≤ j) :
-- imply
  i.val ≤ j.val := by
-- proof
  simp_all


-- created on 2025-06-21
