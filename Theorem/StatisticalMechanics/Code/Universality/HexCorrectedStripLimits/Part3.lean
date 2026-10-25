/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part14
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCSTopWalk_subset_atWidth
    (T L : ℕ) (hT : 0 < T) :
    ∀ ts, HexCSTopWalk T L hT ts → HexCSTopWalkAtWidth T hT ts := by
  intro ts hts
  exact ⟨L, hts⟩


end
end StatMech.Universality
