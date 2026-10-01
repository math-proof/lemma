import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {S : Finset (Fin n → ℤ)}
-- given
  (h : S.card = 1) :
-- imply
  ∑ x ∈ S, x ∈ S := by
-- proof
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
  simp


-- created on 2026-09-27
