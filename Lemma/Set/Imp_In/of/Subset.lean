import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
-- given
  (h : ∀ x, x ∈ A → x ∈ B) :
-- imply
  A ⊆ B := by
-- proof
  intro x hx
  exact h x hx


-- created on 2022-09-20
