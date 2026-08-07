import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
  (f : α → Set β)
-- given
  (h : A = B) :
-- imply
  ⋃ x ∈ A, f x = ⋃ x ∈ B, f x := by
-- proof
  rw [h]


-- created on 2026-08-07
