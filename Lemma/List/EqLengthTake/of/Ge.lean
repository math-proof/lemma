import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length ≥ l) :
-- imply
  (a.take l).length = l := by
-- proof

  simp [h]


-- created on 2025-05-02
