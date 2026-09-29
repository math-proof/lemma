import sympy.concrete.continuant
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℤ}
-- given
  (h₀ : n > 0)
  (h : ∀ i < n, x i ≥ 1) :
-- imply
  K x n > 0 := by
-- proof
  have key : ∀ m, m + 1 ≤ n → K x m ≥ 0 ∧ K x (m + 1) ≥ 1 := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [K]
    | succ m ih =>
      intro hm
      obtain ⟨h0, h1⟩ := ih (by omega)
      refine ⟨by linarith, ?_⟩
      rw [K]
      have hx := h (m + 1) (by omega)
      nlinarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := (key m le_rfl).2
  omega


-- created on 2026-09-27
