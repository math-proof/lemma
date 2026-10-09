import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {n : ℕ}
  {k j : ℤ}
  {f : (Fin n → ℝ) → ℤ}
  {g : ℤ → ℤ}
  {f' : ℤ → (Fin n → ℝ) → ℤ}
-- given
  (h : ∃ x, f x > 0 ∧ (g j > f' j x ∧ ∃ i ∈ Finset.Ico 0 k, i = j)) :
-- imply
  ∃ x, f x > 0 ∧ ∃ i ∈ Finset.Ico 0 k, g i > f' j x ∧ i = j := by
-- proof
  obtain ⟨x, hx, hg, i, hi, rfl⟩ := h
  exact ⟨x, hx, i, hi, hg, rfl⟩


-- created on 2019-02-27
