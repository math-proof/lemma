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
import Abbrev.v1.Atlas.DifferentialAnalysis.code.SobolevHilbert


noncomputable section

open MeasureTheory

namespace SobolevHilbert

attribute [local instance] sobolevSpace_nacg


/-- The `j`-th iterated derivative of `c • u` is in `L^2` for scalar `c` and `u ∈ SobolevSpace n m`. -/
theorem sobolevSpace_smul_memLp {n m : ℕ}
    (c : ℂ) (u : SobolevEmbedding.SobolevSpace n m) (j : ℕ) (hj : j ≤ m) :
    MemLp (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  by_cases hc : c = 0
  ·
    subst hc
    simp only [zero_smul]
    have : (fun x => iteratedFDeriv ℝ j (0 : EuclideanSpace ℝ (Fin n) → ℂ) x) = 0 := by
      ext x; simp
    rw [this]
    exact MemLp.zero
  ·
    let g : ℂ ≃L[ℝ] ℂ := {
      toLinearEquiv := {
        toLinearMap := (c • (ContinuousLinearMap.id ℝ ℂ)).toLinearMap
        invFun := fun y => c⁻¹ • y
        left_inv := fun y => by simp [← mul_assoc, inv_mul_cancel₀ hc]
        right_inv := fun y => by simp [← mul_assoc, mul_inv_cancel₀ hc]
      }
      continuous_toFun := (c • (ContinuousLinearMap.id ℝ ℂ)).continuous
      continuous_invFun := (c⁻¹ • (ContinuousLinearMap.id ℝ ℂ)).continuous
    }
    have hgf : c • u.toFun = ⇑g ∘ u.toFun := by ext y; simp [g]
    have key : ∀ x, iteratedFDeriv ℝ j (c • u.toFun) x =
        g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDeriv ℝ j u.toFun x) := by
      intro x; rw [hgf]; exact ContinuousLinearEquiv.iteratedFDeriv_comp_left g
    have key2 : ∀ x, g.toContinuousLinearMap.compContinuousMultilinearMap
        (iteratedFDeriv ℝ j u.toFun x) = c • (iteratedFDeriv ℝ j u.toFun x) := by
      intro x
      ext v
      simp [g, ContinuousLinearMap.compContinuousMultilinearMap_coe]
    have key3 : (fun x => iteratedFDeriv ℝ j (c • u.toFun) x) =
        c • (fun x => iteratedFDeriv ℝ j u.toFun x) := by
      ext x; rw [key x, key2 x]; rfl
    rw [key3]
    exact (u.iteratedFDeriv_memLp j hj).const_smul c

end SobolevHilbert
end
