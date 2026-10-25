/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part5


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCSPairIncidence_eq_mate {T L : ℕ} (e : HexCSIncidence T L)
    (he : hexCSIsInterior e) :
    hexCSPairIncidence e = (hexCSInteriorMate ⟨e, he⟩).1 := by
  simp [hexCSPairIncidence, he]


end
end StatMech.Universality
