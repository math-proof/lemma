import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A B S : Set ℤ}
-- given
  (h : A = B) :
-- imply
  A ∪ S = B ∪ S ∧ A ∩ S = B ∩ S := by
-- proof
  subst h
  exact ⟨rfl, rfl⟩


-- created on 2020-09-08
