import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α : Type*}
  [DecidableEq α]
  {A B : Finset α}
-- given
  (h : (A ∪ B).card = A.card + B.card) :
-- imply
  A ∩ B = ∅ := by
-- proof
  have hsum := Finset.card_union_add_card_inter A B
  rw [h] at hsum
  exact Finset.card_eq_zero.mp (Nat.add_left_cancel hsum)


-- created on 2021-04-04
