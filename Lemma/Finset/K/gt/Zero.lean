import sympy.concrete.continuant
import sympy.sets.sets
import sympy.Basic
open Continuant


@[main]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i, x i > 0) :
-- imply
  K x n > 0 := by
-- proof
  have key : ∀ m, K x m ≥ 0 ∧ K x (m + 1) > 0 := by
    intro m
    induction m with
    | zero => simp [K]
    | succ m ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨h1.le, ?_⟩
      rw [K]
      have hx := h (m + 1)
      positivity
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (key m).2


-- created on 2026-09-27
