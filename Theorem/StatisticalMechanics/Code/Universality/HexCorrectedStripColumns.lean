/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMassLimits.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence.Part3


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCSTopWalkAtWidth_width_unique
    {T U : ℕ} {hT : 0 < T} {hU : 0 < U} {ts : List ℤ}
    (hwalkT : HexCSTopWalkAtWidth T hT ts)
    (hwalkU : HexCSTopWalkAtWidth U hU ts) : T = U := by
  obtain ⟨LT, _, _, c, _, hc, hcdepth, hcend⟩ := hwalkT
  obtain ⟨LU, _, _, d, _, hd, hddepth, hdend⟩ := hwalkU
  have hmid : hexAWMid c 0 = hexAWMid d 0 := hcend.symm.trans hdend
  have hcd := (hexAWMid_white_injective hc hd hmid).1
  rw [hcd] at hcdepth
  omega

end
end StatMech.Universality
