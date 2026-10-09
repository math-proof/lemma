import sympy.Basic


@[path]
private lemma main
-- given
  (h : i ≥ n) :
-- imply
  (List.range n)[i]? = none := by
-- proof
  simp [h]


-- created on 2025-05-10
