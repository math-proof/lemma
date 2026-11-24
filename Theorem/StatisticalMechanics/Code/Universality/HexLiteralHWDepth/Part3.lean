module
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
public import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part2


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

theorem hlhd_intervals_reconstruct (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg) :
    hlhd_intervalTurns ts (hlhd_intervals ts hleg) = ts := by
  by_cases hempty : ts = []
  · simp [hempty, hlhd_intervalTurns, hlhd_intervals,
      hlhr_intervalsAux, hlhr_intervalTurns]
  · apply hlhr_intervalsAux_reconstruct (hlhd_height ts hleg) ts
      ts.length 0 true (by omega) (by omega)
    intro _
    exact hlhd_halfSpace_ahead ts hleg hhalf


end
end StatMech.Universality
