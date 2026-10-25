/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part15


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

theorem hexAWPairIncidence_eq_mate {T L : ℕ} (e : HexAWIncidence T L)
    (he : hexAWIsInterior e) :
    hexAWPairIncidence e = (hexAWInteriorMate ⟨e, he⟩).1 := by
  simp [hexAWPairIncidence, he]


end
end StatMech.Universality
