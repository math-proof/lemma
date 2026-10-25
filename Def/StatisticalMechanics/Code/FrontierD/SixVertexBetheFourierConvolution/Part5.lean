/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part4


namespace StatMech.FrontierD

noncomputable section

def XiFourierTermMulRootDensityContinuous
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) : C(Real, Real) :=
  ⟨fun beta => sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
      sixVertexFourierRootDensity lam beta, by
    exact (by
      unfold sixVertexXiFourierTerm
      fun_prop : Continuous _).mul (continuous_sixVertexFourierRootDensity hlam)⟩


end
end StatMech.FrontierD
