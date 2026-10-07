import sympy.concrete.continuant
import sympy.Basic
open Continuant


@[main]
private lemma main
-- given
  (x : ℕ → ℝ) :
-- imply
  ∀ m, (∀ i, 1 ≤ i → i < m + 1 → 0 < x i) → 0 ≤ K x m ∧ 0 < K x (m + 1) := by
-- proof
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨by simp [K], by simp [K]⟩
  | succ m ih =>
    intro h
    obtain ⟨h0, h1⟩ := ih (fun i h1 h2 => h i h1 (by omega))
    refine ⟨h1.le, ?_⟩
    show 0 < K x (m + 1) * x (m + 1) + K x m
    exact add_pos_of_pos_of_nonneg (mul_pos h1 (h (m + 1) (by omega) (by omega))) h0


-- created on 2026-10-07
