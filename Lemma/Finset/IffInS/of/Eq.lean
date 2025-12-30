import sympy.Basic


@[main]
private lemma main
  {A B : Finset ι}
-- given
  (h : A = B)
  (x : ι) :
-- imply
  x ∈ A ↔ x ∈ B := by
-- proof
  rw [h]


-- created on 2025-12-30
