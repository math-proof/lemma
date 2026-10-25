/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateBoundaryLimit
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor.Part2


namespace StatMech.FrontierD

noncomputable section

theorem lipschitzWith_sixVertexRegularizedBetheLogNormDerivative
    {c epsilon : Real} (hc : 2 < c) (hepsilon : 0 < epsilon) :
    LipschitzWith
      (sixVertexRegularizedBetheLogNormSecondDerivativeNNReal c epsilon)
      (sixVertexRegularizedBetheLogNormDerivative c epsilon) := by
  have hboundNonneg : 0 <=
      sixVertexRegularizedBetheLogNormSecondDerivativeBound c epsilon := by
    unfold sixVertexRegularizedBetheLogNormSecondDerivativeBound
    have hd : 0 < c ^ 2 - 2 := by nlinarith
    have ha : 0 < c ^ 2 - 1 := by nlinarith
    positivity
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_sixVertexRegularizedBetheLogNormDerivative
      hc hepsilon).differentiableAt
  · intro x
    rw [(hasDerivAt_sixVertexRegularizedBetheLogNormDerivative
      hc hepsilon).deriv]
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm]
    change |sixVertexRegularizedBetheLogNormSecondDerivative c epsilon x| <= _
    rw [show (sixVertexRegularizedBetheLogNormSecondDerivativeNNReal
        c epsilon : Real) =
      sixVertexRegularizedBetheLogNormSecondDerivativeBound c epsilon by
        exact Real.coe_toNNReal _ hboundNonneg]
    exact abs_sixVertexRegularizedBetheLogNormSecondDerivative_le hc hepsilon

end
end StatMech.FrontierD
