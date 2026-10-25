/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part17


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexAWRightFixedIncidence (k L : ℕ) (hk : 0 < k) :
    HexAWIncidence (2 * k) L :=
  ⟨⟨hexAWRightFixedCoord k, hexAWRightFixedCoord_mem k L hk⟩, 0⟩

end
end StatMech.Universality
