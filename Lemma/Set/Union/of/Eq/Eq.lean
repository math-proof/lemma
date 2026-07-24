import sympy.Basic


@[main]
private lemma main
  {A B X Y : Set α}
-- given
  (h₀ : A = B)
  (h₁ : X = Y) :
-- imply
  A ∪ X = B ∪ Y := by
-- proof
  rw [h₀, h₁]


-- created on 2025-04-05
