import sympy.Basic
import sympy.sets.sets
open Set


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A = B) :
-- imply
  (∀ x, x ∈ A → x ∈ B) ∧ (∀ x, x ∈ B → x ∈ A) := by
-- proof
  subst h
  exact ⟨fun _ hx => hx, fun _ hx => hx⟩


-- created on 2026-10-03
