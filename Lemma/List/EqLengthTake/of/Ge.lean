import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ l) :
-- imply
  (s.take l).length = l := by
-- proof
  simp [h]


-- created on 2025-05-02
