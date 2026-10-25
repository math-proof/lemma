/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevHilbert.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.HilbertSpace
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
import Class.v1.Atlas.DifferentialAnalysis.code.HilbertSpace
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Instance.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert.Part4


noncomputable section

open MeasureTheory

namespace SobolevHilbert

attribute [local instance] sobolevSpace_nacg


/-- The Sobolev norm is homogeneous (bounded by) `‖c‖ * ‖u‖` under scalar multiplication. -/
theorem sobolevSpace_norm_smul_le {n m : ℕ}
    (c : ℂ) (u : SobolevEmbedding.SobolevSpace n m) :
    @Norm.norm _ (sobolevSpace_nacg n m).toNorm (c • u) ≤
      ‖c‖ * @Norm.norm _ (sobolevSpace_nacg n m).toNorm u := by

  show sobolevNorm (c • u) ≤ ‖c‖ * sobolevNorm u
  simp only [sobolevNorm, sobolevSpace_smul_toFun]

  have hderiv : ∀ j, j ≤ m → ∀ x : EuclideanSpace ℝ (Fin n),
      iteratedFDeriv ℝ j (c • u.toFun) x = c • iteratedFDeriv ℝ j u.toFun x := by
    intro j hj x
    exact iteratedFDeriv_const_smul_apply (sobolevSpace_contDiff u j hj).contDiffAt

  have heLp : ∀ j ∈ Finset.range (m + 1),
      eLpNorm (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) 2 volume =
        ‖c‖ₑ * eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume := by
    intro j hj
    have hjm : j ≤ m := by rw [Finset.mem_range] at hj; omega
    have heq : (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) =
        c • (fun x => iteratedFDeriv ℝ j u.toFun x) := by
      ext x; simp [hderiv j hjm x]
    rw [heq]
    exact eLpNorm_const_smul c _ 2 volume

  have htoReal : ∀ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) 2 volume).toReal =
        ‖c‖ * (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal := by
    intro j hj
    rw [heLp j hj, ENNReal.toReal_mul]
    simp [enorm]

  have hsq : ∀ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) 2 volume).toReal ^ 2 =
        ‖c‖ ^ 2 * (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal ^ 2 := by
    intro j hj
    rw [htoReal j hj, mul_pow]

  have hsum : (∑ j ∈ Finset.range (m + 1),
      (eLpNorm (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) 2 volume).toReal ^ 2) =
      ‖c‖ ^ 2 * (∑ j ∈ Finset.range (m + 1),
        (eLpNorm (fun x => iteratedFDeriv ℝ j u.toFun x) 2 volume).toReal ^ 2) := by
    rw [Finset.sum_congr rfl hsq, ← Finset.mul_sum]

  rw [hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]

end SobolevHilbert
end
