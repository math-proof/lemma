/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part4


namespace StatMech.Universality

open HexWalk

noncomputable section

structure HLHCMidpointColumnWalk (T : ℕ) (ts : List ℤ) where
  legal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW
  midCoord : Fin ts.length → HexAWCoord
  midEdge : Fin ts.length → Fin 3
  incident : ∀ k : Fin ts.length,
    hexInfra_midAccum hexAWStart 1 (ts.take k.1) =
      hexAWMid (midCoord k) (midEdge k)
  horizontal : ∀ k : Fin ts.length,
    0 ≤ hexAWBookRe2 (midCoord k) ∧
      hexAWBookRe2 (midCoord k) ≤ 3 * T
  topCoord : HexAWCoord
  top_white : topCoord.color = .white
  top_depth : hexAWDepth topCoord = T
  endsAt : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid topCoord 0)

end
end StatMech.Universality
