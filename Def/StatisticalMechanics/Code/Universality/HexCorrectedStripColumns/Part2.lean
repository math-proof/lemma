/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMassLimits.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumns.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hexCSTopFiberEquiv (T : ℕ) (hT : 0 < T) :
    {ts : List ℤ // HexCSTopWalkAtWidth T hT ts} ≃
      {w : {ts : List ℤ // HexCSTopWalkAnyWidth ts} //
        hexCSTopWalkWidth w = T} where
  toFun w := ⟨⟨w.1, T, hT, w.2⟩,
    hexCSTopWalkWidth_eq ⟨w.1, T, hT, w.2⟩ hT w.2⟩
  invFun w := ⟨w.1.1, by
    have hs := hexCSTopWalkWidth_spec w.1
    simpa [w.2] using hs⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

end
end StatMech.Universality
