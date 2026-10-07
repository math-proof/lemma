import sympy.concrete.continuant
import sympy.Basic
open Continuant


@[main]
private lemma main
-- given
  (x : ℕ → ℝ) :
-- imply
  ∀ m, (K x (m + 1) = H (fun i => x (i + 1)) m ∧
      H x (m + 1) = x 0 * K x (m + 1) + K (fun i => x (i + 1)) m) ∧
    (K x (m + 2) = H (fun i => x (i + 1)) (m + 1) ∧
      H x (m + 2) = x 0 * K x (m + 2) + K (fun i => x (i + 1)) (m + 1)) := by
-- proof
  intro m
  induction m with
  | zero =>
    refine ⟨⟨rfl, ?_⟩, ?_, ?_⟩
    ·
      show x 0 = x 0 * 1 + 0
      ring
    ·
      show 1 * x 1 + 0 = x (0 + 1)
      ring
    ·
      show x 0 * x 1 + 1 = x 0 * (1 * x 1 + 0) + 1
      ring
  | succ m ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_, ?_⟩
    ·
      show K x (m + 2) * x (m + 2) + K x (m + 1) =
        H (fun i => x (i + 1)) (m + 1) * x (m + 1 + 1) + H (fun i => x (i + 1)) m
      rw [h0.1, h1.1]
    ·
      show H x (m + 2) * x (m + 2) + H x (m + 1) =
        x 0 * (K x (m + 2) * x (m + 2) + K x (m + 1)) +
          (K (fun i => x (i + 1)) (m + 1) * x (m + 1 + 1) + K (fun i => x (i + 1)) m)
      rw [h0.2, h1.2]
      ring


-- created on 2026-10-07
