import sympy.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (h : i ≥ v.length) :
-- imply
  v[i]? = none := by
-- proof
  simp [h]


-- created on 2025-05-10
