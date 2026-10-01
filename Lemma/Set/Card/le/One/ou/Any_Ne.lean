import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Finset ℝ} :
-- imply
  S.card ≤ 1 ∨ ∃ x ∈ S, ∃ y ∈ S, x ≠ y := by
-- proof
  by_cases hS : S.card ≤ 1
  · exact Or.inl hS
  · exact Or.inr (Finset.one_lt_card.mp (by omega))


-- created on 2026-09-27
