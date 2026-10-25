import Mathlib
import sympy.Basic
import Structure.v1.Atlas.ProjectionTheory.code.DoubleCountingRealCor
open Finset BigOperators ProjectionTheory


namespace ProjectionTheory

/--
[double_counting_real_hausdorff_dichotomy_line683](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingRealCor.lean)
-/
@[path]
lemma double_counting_real_hausdorff_dichotomy_line683
  {setup : DoubleCountingRealHausdorffSetup}
-- given
  (hX_pos : 0 < setup.cardX)
  (hD_pos : 0 < setup.cardD)
  (hR_gt : 1 < setup.R)
  (h_intermediate : ∃ C : ℝ, C > 0 ∧ (setup.cardD : ℝ) ≤ C * Real.log setup.R * ((setup.S : ℝ) + (setup.S : ℝ) * (setup.cardD : ℝ) / (setup.cardX : ℝ))) :
-- imply
  ∃ C : ℝ, C > 0 ∧ ((setup.S : ℝ) ≥ (setup.cardX : ℝ) / (C * Real.log setup.R) ∨ (setup.cardD : ℝ) ≤ C * Real.log setup.R * (setup.S : ℝ)) := by
-- proof
  obtain ⟨C, hC_pos, hbound⟩ := h_intermediate
  have hlogR_pos : (0 : ℝ) < Real.log setup.R := Real.log_pos hR_gt
  have hX_pos' : (0 : ℝ) < (setup.cardX : ℝ) := Nat.cast_pos.mpr hX_pos
  have hD_nn : (0 : ℝ) ≤ (setup.cardD : ℝ) := Nat.cast_nonneg' _
  refine ⟨2 * C, by linarith, ?_⟩
  by_cases h : C * Real.log setup.R * (setup.S : ℝ) / (setup.cardX : ℝ) ≥ 1 / 2
  ·
    left
    rw [ge_iff_le, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * C * Real.log setup.R)]
    have h' : 1 / 2 * (setup.cardX : ℝ) ≤ C * Real.log setup.R * (setup.S : ℝ) := by
      rwa [ge_iff_le, le_div_iff₀ hX_pos'] at h
    nlinarith
  ·
    right
    simp only [ge_iff_le, not_le] at h
    have key : (setup.cardD : ℝ) * (setup.cardX : ℝ) ≤
      C * Real.log setup.R * (setup.S : ℝ) * (setup.cardX : ℝ) +
      C * Real.log setup.R * (setup.S : ℝ) * (setup.cardD : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_right hbound (le_of_lt hX_pos')
      have eq1 : C * Real.log setup.R *
        ((setup.S : ℝ) + (setup.S : ℝ) * (setup.cardD : ℝ) / (setup.cardX : ℝ)) *
        (setup.cardX : ℝ) =
        C * Real.log setup.R * (setup.S : ℝ) * (setup.cardX : ℝ) +
        C * Real.log setup.R * (setup.S : ℝ) * (setup.cardD : ℝ) := by
        have hX_ne : (setup.cardX : ℝ) ≠ 0 := ne_of_gt hX_pos'
        field_simp
      linarith
    have h2 : C * Real.log setup.R * (setup.S : ℝ) * 2 < (setup.cardX : ℝ) := by
      have := (div_lt_iff₀ hX_pos').mp h
      linarith
    nlinarith
/-- **Corollary (Real SETUP with Hausdorff spacing).** Under the `ℝ`-SETUP where both
`X` and `D` have Hausdorff spacing, `|D| ≲ S · R / |X|`. -/

end ProjectionTheory


-- created on 2026-10-23
