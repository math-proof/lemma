import sympy.concrete.continued_fraction
import sympy.Basic
open Continuant


@[path]
private lemma main
-- given
  (x : ℕ → ℝ)
  (h : ∀ i, 0 < x i) :
-- imply
  ∀ m, 0 ≤ K x m ∧ 0 < K x (m + 1) := by
-- proof
  intro p₀
  match p₀ with
  | 0 => exact ⟨by simp [K], by simp [K]⟩
  | m + 1 =>
    have ih := main x h m
    exact ⟨ih.2.le, show 0 < K x (m + 1) * x (m + 1) + K x m from
      add_pos_of_pos_of_nonneg (mul_pos ih.2 (h (m + 1))) ih.1⟩


-- created on 2026-10-07
