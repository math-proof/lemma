import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
  {x : α}
-- given
  (h : A ⊆ B)
  (hx : x ∈ A) :
-- imply
  x ∈ B := by
-- proof
  exact h hx


-- created on 2022-09-20
