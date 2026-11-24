module
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part21


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhd_intervalTopCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : HexAWCoord :=
  let far := hlhd_intervalFarCoord ts hleg hhalf p hp
  if far.color = .white then far else hexAWNeighbor far 0

end
end StatMech.Universality
