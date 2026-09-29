import sympy.sets.sets
import sympy.Basic


@[main]
private lemma size_deduction
  {S : Finset ℤ}
  {n : ℕ}
-- given
  (h₀ : n > 0)
  (h : S.card = n) :
-- imply
  ∃ x ∈ S, (S \ {x}).card = n - 1 := by
-- proof
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  exact ⟨x, hx, by rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hx, h]⟩


-- created on 2026-09-27
