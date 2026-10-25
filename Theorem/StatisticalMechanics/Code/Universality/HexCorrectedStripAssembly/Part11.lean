/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part12


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

@[simp] theorem hexCSBoundaryFixed_piece
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (k : HexCSFixedIndex T L hT) :
    (hexCSBoundaryFixed T L hT hlocal hlaw k).piece = hexCSFixedPiece k := by
  simp [hexCSBoundaryFixed, HexFixedBoundaryPoint.piece, hexCSFixedPiece,
    endpointFixedBoundaryPoint_of_winding]


end
end StatMech.Universality
