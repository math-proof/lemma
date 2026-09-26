import sympy.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Lattice
open Finset


@[main]
private lemma main
  {E F α : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [Fintype α] [Nonempty α]
  {f : E → α → F}
-- given
  (h : ∃ C, 0 ≤ C ∧ ∀ x y z, ‖f x z - f y z‖ ≤ C * ‖x - y‖) :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ x z, ‖f x z‖ ≤ C * (‖x‖ + 1) := by
-- proof
  obtain ⟨C, hC, hf⟩ := h
  set CF := univ.sup' univ_nonempty fun z => ‖f 0 z‖
  have hCF : ∀ z, ‖f 0 z‖ ≤ CF := fun z => le_sup' (fun z => ‖f 0 z‖) (mem_univ z)
  refine ⟨max C CF, le_max_of_le_left hC, fun x z => ?_⟩
  have h₁ := hf x 0 z
  rw [sub_zero] at h₁
  calc ‖f x z‖ ≤ ‖f x z - f 0 z‖ + ‖f 0 z‖ := norm_le_norm_sub_add _ _
    _ ≤ max C CF * ‖x‖ + max C CF :=
      add_le_add (h₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
        ((hCF z).trans (le_max_right _ _))
    _ = _ := by ring


-- created on 2026-09-26