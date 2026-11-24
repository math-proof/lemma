module
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part18


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

noncomputable def hlhd_intervalPrevCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : HexAWCoord :=
  hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
    (hlhc_prefixCoord ts hleg.1 p.1)
    (hlhc_prefixCoord ts hleg.1 (p.2 - 1))

noncomputable def hlhd_intervalFarCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : HexAWCoord :=
  hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
    (hlhc_prefixCoord ts hleg.1 p.1)
    (hlhc_prefixCoord ts hleg.1 p.2)

end
end StatMech.Universality
