import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : i ≥ j) :
-- imply
  (s.take i).take j = s.take j := by
-- proof
  rw [List.take_take]
  simp [h]


-- created on 2025-06-14
