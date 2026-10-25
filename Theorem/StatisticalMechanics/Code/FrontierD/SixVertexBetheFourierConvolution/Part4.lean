/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part4


namespace StatMech.FrontierD

noncomputable section

theorem intervalIntegral_XiFourierTerm_mul_rootDensity
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) :
    (∫ beta in -Real.pi..Real.pi,
      sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
        sixVertexFourierRootDensity lam beta) =
      sixVertexXiRootConvolutionTerm lam n alpha := by
  unfold sixVertexXiFourierTerm sixVertexXiRootConvolutionTerm
  simp_rw [show ∀ beta : Real,
      (2 * Real.exp (-((n + 1 : Real) * (2 * lam))) *
          Real.cos ((n + 1 : Real) * (alpha - beta))) *
          sixVertexFourierRootDensity lam beta =
        (2 * Real.exp (-((n + 1 : Real) * (2 * lam)))) *
          (Real.cos ((n + 1 : Real) * (alpha - beta)) *
            sixVertexFourierRootDensity lam beta) by
      intro beta
      ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_shiftedCos_mul_sixVertexFourierRootDensity hlam]
  ring

end
end StatMech.FrontierD
