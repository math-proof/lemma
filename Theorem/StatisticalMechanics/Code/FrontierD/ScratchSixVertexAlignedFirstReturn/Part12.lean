/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part14
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem doubledAlignedBlackDart_first_step
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    fkMedialBlackBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree false)
        (doubledAlignedBlackDart homega heta hdegree false x) =
      fkMedialBlackBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree true)
        (doubledAlignedBlackDart homega heta hdegree true x) := by
  rcases x with ⟨d, branch⟩
  let v := d.1.1.1
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree d.1
  let d0 := orientedDisagreementDartAtActiveVertex
    homega heta v hactive
  have hd0 : d0 = d := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d0 d rfl
  have hP := alignedRoutingPairing_eq_at_active
    homega heta hdegree false v hactive
  have hQ := alignedRoutingPairing_eq_at_active
    homega heta hdegree true v hactive
  change alignedRoutingPairing homega heta hdegree false v =
      (orientedDartAlignedRetie homega heta hdegree d0).pairingP at hP
  change alignedRoutingPairing homega heta hdegree true v =
      (orientedDartAlignedRetie homega heta hdegree d0).pairingQ at hQ
  rw [hd0] at hP hQ
  change fkMedialBlackBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree false)
        (blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree false)
          (v, if branch then
            !strandSlot
              (orientedDartAlignedRetie homega heta hdegree d).pairingP
                d.1.1.2
          else strandSlot
              (orientedDartAlignedRetie homega heta hdegree d).pairingP
                d.1.1.2)) =
      fkMedialBlackBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree true)
        (blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree true)
          (v, if branch then
            !boundaryAlignedSlotQRaw (fkMedialVertexParity v)
              (orientedDartAlignedRetie homega heta hdegree d).pairingP
              (orientedDartAlignedRetie homega heta hdegree d).pairingQ
                d.1.1.2
          else boundaryAlignedSlotQRaw (fkMedialVertexParity v)
              (orientedDartAlignedRetie homega heta hdegree d).pairingP
              (orientedDartAlignedRetie homega heta hdegree d).pairingQ
                d.1.1.2))
  exact blackBoundary_alignedSlot_first_step
    (alignedRoutingLoopPairing homega heta hdegree false)
    (alignedRoutingLoopPairing homega heta hdegree true) v
    (orientedDartAlignedRetie homega heta hdegree d).pairingP
    (orientedDartAlignedRetie homega heta hdegree d).pairingQ branch
    d.1.1.2 hP hQ

end ScratchLocalRetieC
