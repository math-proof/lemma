import sympy.Basic


@[main]
private lemma main
  {A B X Y : Set α}
-- given
  (h₀ : A ⊆ B)
  (h₁ : X ⊆ Y) :
-- imply
  A ∪ X ⊆ B ∪ Y := by
-- proof
  grind


-- created on 2018-04-21
-- updated on 2026-08-04
