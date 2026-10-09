import sympy.concrete.continued_fraction
import sympy.Basic
open Continuant


@[path]
private lemma main
-- given
  (x : ℕ → ℝ)
  (h : ∀ i, 0 < x i)
  (m : ℕ) :
-- imply
  0 < H x m := by
-- proof
  refine ((?_ : ∀ m, 0 < H x m ∧ 0 < H x (m + 1)) m).left
  intro m
  induction m with
  | zero => exact ⟨by simp [H], by simpa [H] using h 0⟩
  | succ m ih =>
    exact ⟨ih.2, show 0 < H x (m + 1) * x (m + 1) + H x m from
      add_pos (mul_pos ih.2 (h (m + 1))) ih.1⟩


-- created on 2026-10-07
