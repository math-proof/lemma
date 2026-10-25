/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part14
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample


namespace StatMech.FrontierD

set_option maxHeartbeats 2000000 in
theorem sixVertexFourByTwoAlignedPairings_false
    (d : SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows) :
    let retie := orientedDartAlignedRetie
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo d
    retie.pairingP = false ∧ retie.pairingQ = false := by
  let retie := orientedDartAlignedRetie
    sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
    sixVertexFourByTwo_locallyDegreeTwo d
  have hP := retie.compatibleP
  have hQ := retie.compatibleQ
  have hpartner := retie.partnerDisagrees
  have hside := sixVertexDisagreementDart_side_mem d.1
  rw [mem_sixVertexLocalDisagreementSides] at hside
  rcases d with ⟨⟨⟨⟨x, y⟩, side⟩, hdisagree⟩, hincoming⟩
  fin_cases x <;> fin_cases y <;> fin_cases side <;>
    cases hp : retie.pairingP <;> cases hq : retie.pairingQ
  all_goals
    first
    | exact ⟨hp, hq⟩
    | simp_all [retie, compatible, localMate, sixVertexLocalIncomingPattern,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, sixVertexFourByTwoLowArrows,
      sixVertexFourByTwoHighArrows, sixVertexFourByTwoTorus,
      sixVertexFourByTwoVertex, SixVertexArrows.cyclicPred]

theorem sixVertexFourByTwoAlignedRoutingPairing_false
    (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex) :
    alignedRoutingPairing sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo layer v = false := by
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern sixVertexFourByTwoLowArrows v)
      (sixVertexLocalIncomingPattern sixVertexFourByTwoHighArrows v)).card = 2 := by
    rw [card_sixVertexLocalDisagreementSides]
    exact sixVertexFourByTwo_localDisagreementDegree_two v
  rw [alignedRoutingPairing_eq_at_active
    sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
    sixVertexFourByTwo_locallyDegreeTwo layer v hactive]
  dsimp only
  obtain ⟨hP, hQ⟩ := sixVertexFourByTwoAlignedPairings_false
    (orientedDisagreementDartAtActiveVertex
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice v
      hactive)
  cases layer <;> simp [hP, hQ]

theorem sixVertexFourByTwoAlignedRoutingPairing_false_funext (layer : Bool) :
    alignedRoutingPairing sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo layer = fun _ => false := by
  funext v
  exact sixVertexFourByTwoAlignedRoutingPairing_false layer v

end StatMech.FrontierD
