/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Abbrev.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part3


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

def hexAWInteriorMate {T L : ℕ}
    (e : HexAWInteriorIncidence T L) : HexAWInteriorIncidence T L := by
  let v' : HexAWVertex T L :=
    ⟨hexAWNeighbor e.1.vtx.1 e.1.edge, e.2⟩
  let e' : HexAWIncidence T L := ⟨v', e.1.edge⟩
  refine ⟨e', ?_⟩
  change hexAWNeighbor v'.1 e.1.edge ∈ hexAWVertexSet T L
  simp [v']

end
end StatMech.Universality
