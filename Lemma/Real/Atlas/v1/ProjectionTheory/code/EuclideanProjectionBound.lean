import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProjectionTheory.code.EuclideanProjectionBound
open ProjectionTheory


namespace ProjectionTheory

/--
[dyadic_scale_count_le_log](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/EuclideanProjectionBound.lean)
-/
@[path]
lemma dyadic_scale_count_le_log
  {d : EuclideanProjectionData} :
-- imply
  (numDyadicScales d : ℝ) ≤ Real.logb 2 d.R + 2 := by
-- proof
  unfold numDyadicScales
  push_cast
  have hR_pos : (0 : ℝ) < d.R := by linarith [d.hR]
  have hceil_pos : 0 < Nat.ceil d.R := Nat.ceil_pos.mpr hR_pos
  have h1 : (Nat.log 2 (Nat.ceil d.R) : ℝ) ≤ Real.logb 2 (Nat.ceil d.R : ℝ) := by
    have := Real.natLog_le_logb (Nat.ceil d.R) 2
    simp only [Nat.cast_ofNat] at this
    exact this
  have h2 : Real.logb 2 (Nat.ceil d.R : ℝ) ≤ Real.logb 2 d.R + 1 := by
    have hceil_bound : (Nat.ceil d.R : ℝ) ≤ 2 * d.R := by
      have h := Nat.ceil_lt_add_one (le_of_lt hR_pos)
      linarith [d.hR]
    calc Real.logb 2 (Nat.ceil d.R : ℝ)
      ≤ Real.logb 2 (2 * d.R) := by
        apply Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
        · exact Nat.cast_pos.mpr hceil_pos
        · exact hceil_bound
      _ = Real.logb 2 2 + Real.logb 2 d.R := by
        rw [Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hR_pos)]
      _ = 1 + Real.logb 2 d.R := by
        rw [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
      _ = Real.logb 2 d.R + 1 := by ring
  linarith
/-- Upper bound on the wave packet `L²`-energy obtained by summing the per-scale
estimates over the `log₂ R + 2` dyadic scales:
`‖f‖² ≤ S · |D| · R · (log₂ R + 2) · max_{r ∈ [1,R]} (N_X(r) N_D(r/R) / r²)`. -/

end ProjectionTheory


-- created on 2026-10-23
