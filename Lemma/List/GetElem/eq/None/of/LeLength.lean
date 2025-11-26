import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≤ i) :
-- imply
  s[i]? = none := by
-- proof
  simp [h]


-- created on 2025-05-10
