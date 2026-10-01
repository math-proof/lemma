import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A B S : Set ℤ}
-- given
  (h : A = B) :
-- imply
  A ∪ S = B ∪ S ∧ A ∩ S = B ∩ S := by
-- proof
  subst h
  exact ⟨rfl, rfl⟩


-- created on 2026-09-27
