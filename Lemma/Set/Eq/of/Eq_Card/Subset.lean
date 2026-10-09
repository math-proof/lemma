import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A B : Finset ℤ}
-- given
  (h₀ : A.card = B.card)
  (h₁ : A ⊆ B) :
-- imply
  A = B := by
-- proof
  exact Finset.eq_of_subset_of_card_le h₁ h₀.symm.le


-- created on 2020-07-20
