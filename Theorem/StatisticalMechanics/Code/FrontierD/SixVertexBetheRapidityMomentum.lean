/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierKernelClosedForm


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexXiFourier_pos
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    0 < sixVertexXiFourier lam alpha := by
  rw [sixVertexXiFourier_eq hlam]
  exact div_pos (Real.sinh_pos_iff.mpr hlam)
    (by
      have hcosh : 1 < Real.cosh lam := Real.one_lt_cosh.mpr hlam.ne'
      linarith [Real.cos_le_one alpha])

theorem sixVertexXiFourier_neg (lam alpha : Real) :
    sixVertexXiFourier lam (-alpha) = sixVertexXiFourier lam alpha := by
  unfold sixVertexXiFourier sixVertexXiFourierTerm
  congr 1
  apply tsum_congr
  intro n
  rw [mul_neg, Real.cos_neg]

end
end StatMech.FrontierD
