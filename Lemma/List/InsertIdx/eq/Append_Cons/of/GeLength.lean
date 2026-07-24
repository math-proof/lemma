import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ i)
  (x : α) :
-- imply
  s.insertIdx i x = s.take i ++ x :: s.drop i := by
-- proof
  induction s generalizing i with
  | nil =>
    simp_all
  | cons hd tl ih =>
    cases i <;>
      simp_all


-- created on 2025-11-27
