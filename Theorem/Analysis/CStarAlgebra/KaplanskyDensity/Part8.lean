/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Def.Analysis.CStarAlgebra.KaplanskyDensity.Part8
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapOffDiag

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The adjoint of `star x` is `x`. -/
theorem kapAdjoint_star (x : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (star x) = x := by
  rw [← ContinuousLinearMap.star_eq_adjoint, star_star]

/-- Star swaps the first off-diagonal summand to the second. -/
theorem kapOffDiag_star_fst (x : H →L[ℂ] H) :
    star (kapInl ∘L x ∘L kapSnd) = kapInr ∘L star x ∘L kapFst := by
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc, kapAdjoint_inl, kapAdjoint_snd]

/-- Star swaps the second off-diagonal summand to the first. -/
theorem kapOffDiag_star_snd (x : H →L[ℂ] H) :
    star (kapInr ∘L star x ∘L kapFst) = kapInl ∘L x ∘L kapSnd := by
  conv_lhs => rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    kapAdjoint_inr, kapAdjoint_fst, kapAdjoint_star,
    ContinuousLinearMap.comp_assoc]

/-- The off-diagonal lift is self-adjoint. -/
theorem kapOffDiag_selfAdjoint (x : H →L[ℂ] H) :
    IsSelfAdjoint (kapOffDiag x) := by
  rw [isSelfAdjoint_iff]
  unfold kapOffDiag
  rw [StarRing.star_add, kapOffDiag_star_fst, kapOffDiag_star_snd, add_comm]

/-- First component of the off-diagonal lift applied to a vector. -/
theorem kapOffDiag_fst_apply (x : H →L[ℂ] H) (v : WithLp 2 (H × H)) :
    kapFst ((kapOffDiag x) v) = x (kapSnd v) := by
  unfold kapOffDiag
  simp only [add_apply, ContinuousLinearMap.comp_apply, map_add,
    kapFst_kapInl_apply, kapFst_kapInr_apply, add_zero]

/-- Second component of the off-diagonal lift applied to a vector. -/
theorem kapOffDiag_snd_apply (x : H →L[ℂ] H) (v : WithLp 2 (H × H)) :
    kapSnd ((kapOffDiag x) v) = star x (kapFst v) := by
  unfold kapOffDiag
  simp only [add_apply, ContinuousLinearMap.comp_apply, map_add,
    kapSnd_kapInl_apply, kapSnd_kapInr_apply, zero_add]

/-- The off-diagonal lift does not increase the norm. -/
theorem kapOffDiag_norm (x : H →L[ℂ] H) (hnorm : ‖x‖ ≤ 1) :
    ‖kapOffDiag x‖ ≤ 1 := by
  have hstar : ‖star x‖ ≤ 1 := by
    rw [norm_star]
    exact hnorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [one_mul]
  have b1 : ‖x (kapSnd v)‖ ≤ ‖kapSnd v‖ := by
    calc ‖x (kapSnd v)‖ ≤ ‖x‖ * ‖kapSnd v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖kapSnd v‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = ‖kapSnd v‖ := one_mul _
  have b2 : ‖star x (kapFst v)‖ ≤ ‖kapFst v‖ := by
    calc ‖star x (kapFst v)‖ ≤ ‖star x‖ * ‖kapFst v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖kapFst v‖ :=
        mul_le_mul_of_nonneg_right hstar (norm_nonneg _)
      _ = ‖kapFst v‖ := one_mul _
  have hsq := kapNorm_sq ((kapOffDiag x) v)
  rw [kapOffDiag_fst_apply, kapOffDiag_snd_apply] at hsq
  have hsqv := kapNorm_sq v
  have g1 : ‖x (kapSnd v)‖ ^ 2 ≤ ‖kapSnd v‖ ^ 2 := by
    nlinarith [b1, sub_nonneg.mpr b1,
      add_nonneg (norm_nonneg (kapSnd v)) (norm_nonneg (x (kapSnd v)))]
  have g2 : ‖star x (kapFst v)‖ ^ 2 ≤ ‖kapFst v‖ ^ 2 := by
    nlinarith [b2, sub_nonneg.mpr b2,
      add_nonneg (norm_nonneg (kapFst v)) (norm_nonneg (star x (kapFst v)))]
  have hle : ‖(kapOffDiag x) v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    linarith [hsq, hsqv, g1, g2]
  have h3 : |‖(kapOffDiag x) v‖| ≤ ‖v‖ :=
    abs_le_of_sq_le_sq hle (norm_nonneg _)
  rwa [abs_of_nonneg (norm_nonneg _)] at h3

/-- The `(1,2)` corner of the off-diagonal lift recovers `x`. -/
theorem kapOffDiag_corner (x : H →L[ℂ] H) :
    kapFst ∘L kapOffDiag x ∘L kapInr = x := by
  ext v
  unfold kapOffDiag
  simp only [ContinuousLinearMap.comp_apply, add_apply, map_zero,
    kapSnd_kapInr_apply, kapFst_kapInr_apply, kapFst_kapInl_apply, add_zero]

end KapOffDiag
end Analysis.CStarAlgebra.KaplanskyDensityWanted
