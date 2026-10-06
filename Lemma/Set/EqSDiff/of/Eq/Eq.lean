import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {α : Type*}
  {A B X Y : Set α}
-- given
  (h₁ : A = B)
  (h₂ : X = Y) :
-- imply
  A \ X = B \ Y := by
-- proof
  rw [h₁, h₂]


-- created on 2021-08-30
