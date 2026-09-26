import sympy.Basic
import Mathlib.Analysis.Normed.Group.Basic


@[main]
private lemma main
  {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  {f : E → F}
-- given
  (h : ∃ C, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖) :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * (‖x‖ + 1) := by
-- proof
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨max C ‖f 0‖, le_max_of_le_left hC, fun x => ?_⟩
  have h₁ := hf x 0
  rw [sub_zero] at h₁
  calc ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
    _ ≤ max C ‖f 0‖ * ‖x‖ + max C ‖f 0‖ :=
      add_le_add (h₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) (le_max_right _ _)
    _ = _ := by ring


-- created on 2026-09-26