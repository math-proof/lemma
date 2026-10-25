/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part15


namespace StatMech.Universality

open HexWalk

noncomputable section

def hlhd_intervalRaw (ts : List ℤ) (p : ℕ × ℕ) : List ℤ :=
  hlhr_intervalContent ts p

noncomputable def hlhd_intervalCore (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : List ℤ :=
  hlhd_coreTurns
    (hlhd_entryTurn (hlhd_intervalFirstEdge ts hleg hhalf p hp))
    (hlhd_intervalRaw ts p)

noncomputable def hlhd_intervalExits (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : Bool :=
  decide (hlhd_intervalLastEdge ts hleg hhalf p hp ≠ 0)

noncomputable def hlhd_intervalEndpoint (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : List ℤ :=
  hlhd_endpointTurns (hlhd_intervalExits ts hleg hhalf p hp)
    (hlhd_exitTurn (hlhd_intervalLastEdge ts hleg hhalf p hp))
    (hlhd_intervalCore ts hleg hhalf p hp)

noncomputable def hlhd_intervalTag (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) : HLHDColumnTag :=
  ⟨hlhd_intervalUp ts hleg hhalf p hp,
    hlhd_turnBit (hlhd_intervalRaw ts p).head!,
    hlhd_intervalExits ts hleg hhalf p hp⟩

end
end StatMech.Universality
