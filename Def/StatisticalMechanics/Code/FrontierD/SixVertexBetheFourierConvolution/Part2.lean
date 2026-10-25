/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution


namespace StatMech.FrontierD

noncomputable section

def shiftedCosMulFourierRootDensityTermContinuous
    (lam : Real) (n j : Nat) (alpha : Real) : C(Real, Real) :=
  ⟨fun beta => Real.cos ((n + 1 : Real) * (alpha - beta)) *
      sixVertexFourierRootDensityTerm lam j beta, by
    unfold sixVertexFourierRootDensityTerm
    fun_prop⟩


end
end StatMech.FrontierD
