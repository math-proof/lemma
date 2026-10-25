/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part24


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhd_intervalMidCoord (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (k : Fin (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
    HexAWCoord :=
  Classical.choose (hlhd_intervalEndpoint_mid_incident_horizontal
    ts hleg hhalf p hp k.1 k.2)

noncomputable def hlhd_intervalMidEdge (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg)
    (k : Fin (hlhd_intervalEndpoint ts hleg hhalf p hp).length) :
    Fin 3 :=
  Classical.choose (Classical.choose_spec
    (hlhd_intervalEndpoint_mid_incident_horizontal
      ts hleg hhalf p hp k.1 k.2))

end
end StatMech.Universality
