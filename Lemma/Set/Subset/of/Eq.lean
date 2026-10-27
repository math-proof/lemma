import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A B : Set ℤ}
-- given
  (h : A = B) :
-- imply
  A ⊆ B := by
-- proof
  rw [h]


-- created on 2020-10-24
