import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : a.length ≥ i)
  (x : α) :
-- imply
  a.insertIdx i x = a.take i ++ x :: a.drop i := by
-- proof
  induction a generalizing i with
  | nil =>
    simp_all
  | cons hd tl ih =>
    cases i <;>
      simp_all


-- created on 2025-11-27
