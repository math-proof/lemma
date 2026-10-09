import sympy.Basic


@[path]
private lemma main
  {A : Set ℤ}
  {f : ℤ → ℤ}
-- given
  (h : {x | f x > 0} = A) :
-- imply
  ∀ x ∈ A, f x > 0 := by
-- proof
  rw [← h]
  exact fun x hx => hx


-- created on 2020-12-26
