import sympy.concrete.continuant
import sympy.Basic
open Continuant


@[main]
private lemma main
-- given
  (x : ℕ → ℝ) :
-- imply
  ∀ m, (∀ i < m + 1, 0 < x i) → 0 < H x m ∧ 0 < H x (m + 1) := by
-- proof
  intro m
  induction m with
  | zero =>
    intro h
    exact ⟨by simp [H], by simpa [H] using h 0 (by omega)⟩
  | succ m ih =>
    intro h
    obtain ⟨h0, h1⟩ := ih (fun i hi => h i (by omega))
    refine ⟨h1, ?_⟩
    show 0 < H x (m + 1) * x (m + 1) + H x m
    exact add_pos (mul_pos h1 (h (m + 1) (by omega))) h0


-- created on 2026-10-07
