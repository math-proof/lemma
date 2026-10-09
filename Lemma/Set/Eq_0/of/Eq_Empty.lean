import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {α : Type*}
  [DecidableEq α]
  {A : Finset α}
-- given
  (h : A = ∅) :
-- imply
  A.card = 0 := by
-- proof
  rw [h, Finset.card_empty]


-- created on 2021-05-14
