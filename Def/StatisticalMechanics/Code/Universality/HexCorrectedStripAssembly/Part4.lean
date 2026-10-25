/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Abbrev.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def hexCSInteriorMate {T L : ℕ}
    (e : HexCSInteriorIncidence T L) : HexCSInteriorIncidence T L := by
  let v' : HexCSVertex T L :=
    ⟨hexAWNeighbor e.1.vtx.1 e.1.edge, e.2⟩
  let e' : HexCSIncidence T L := ⟨v', e.1.edge⟩
  refine ⟨e', ?_⟩
  change hexAWNeighbor v'.1 e.1.edge ∈ hexCSVertexSet T L
  simp [v']

end
end StatMech.Universality
