/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part25


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhd_midpointColumnWalk (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    HLHCMidpointColumnWalk (hlhd_width ts hleg p)
      (hlhd_intervalEndpoint ts hleg hhalf p hp) where
  legal := hlhd_intervalEndpoint_endpointIsLegalSAW ts hleg hhalf p hp
  midCoord := hlhd_intervalMidCoord ts hleg hhalf p hp
  midEdge := hlhd_intervalMidEdge ts hleg hhalf p hp
  incident := fun k => (hlhd_intervalMid_spec ts hleg hhalf p hp k).1
  horizontal := fun k => (hlhd_intervalMid_spec ts hleg hhalf p hp k).2
  topCoord := hlhd_intervalTopCoord ts hleg hhalf p hp
  top_white := hlhd_intervalTopCoord_white ts hleg hhalf p hp
  top_depth := hlhd_intervalTopCoord_depth ts hleg hhalf p hp
  endsAt := hlhd_intervalEndpoint_endsAt ts hleg hhalf p hp


end
end StatMech.Universality
