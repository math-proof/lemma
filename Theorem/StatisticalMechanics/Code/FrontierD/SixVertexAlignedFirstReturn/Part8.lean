/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part9
open StatMech.FrontierD


namespace StatMech.FrontierD

theorem orientedDartAlignedRetie_preserves_localC
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree d
    exchangedLocalCIndicator retie.slotP retie.slotQ
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1) =
      localCIndicator
          (sixVertexLocalIncomingPattern omega d.1.1.1) +
        localCIndicator
          (sixVertexLocalIncomingPattern eta d.1.1.1) := by
  apply canonicalAlignedExitRetie_preserves_localC

theorem orientedDartBoundaryAlignedRetie_nondecreases_localC
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    localCIndicator
          (sixVertexLocalIncomingPattern omega d.1.1.1) +
        localCIndicator
          (sixVertexLocalIncomingPattern eta d.1.1.1) <=
      exchangedLocalCIndicator
        (orientedDartBoundaryAlignedSlot homega heta hdegree false d)
        (orientedDartBoundaryAlignedSlot homega heta hdegree true d)
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1) := by
  change let retie := orientedDartAlignedRetie homega heta hdegree d
    localCIndicator
          (sixVertexLocalIncomingPattern omega d.1.1.1) +
        localCIndicator
          (sixVertexLocalIncomingPattern eta d.1.1.1) <=
      exchangedLocalCIndicator retie.slotP
        (boundaryAlignedSlotQ (fkMedialVertexParity d.1.1.1) retie)
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1)
  apply canonicalAlignedExitRetie_nondecreases_localC

theorem orientedDartBoundaryAlignedMask_nondecreases_localC
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : Bool)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    localCIndicator
          (sixVertexLocalIncomingPattern omega d.1.1.1) +
        localCIndicator
          (sixVertexLocalIncomingPattern eta d.1.1.1) <=
      exchangedLocalAlignedMaskCIndicator select0 select1
        (orientedDartBoundaryAlignedSlot homega heta hdegree false d)
        (orientedDartBoundaryAlignedSlot homega heta hdegree true d)
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1) := by
  let retie := orientedDartAlignedRetie homega heta hdegree d
  change localCIndicator
          (sixVertexLocalIncomingPattern omega d.1.1.1) +
        localCIndicator
          (sixVertexLocalIncomingPattern eta d.1.1.1) <=
      exchangedLocalAlignedMaskCIndicator select0 select1
        (strandSlot retie.pairingP d.1.1.2)
        (boundaryAlignedSlotQRaw (fkMedialVertexParity d.1.1.1)
          retie.pairingP retie.pairingQ d.1.1.2)
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1)
  apply localCIndicator_le_exchange_boundary_aligned_mask
    (sixVertexLocalIncomingPattern omega d.1.1.1)
    (sixVertexLocalIncomingPattern eta d.1.1.1)
    retie.pairingP retie.pairingQ
    (fkMedialVertexParity d.1.1.1) select0 select1 d.1.1.2
  · exact sixVertexLocalIncomingPattern_ice omega homega d.1.1.1
  · exact sixVertexLocalIncomingPattern_ice eta heta d.1.1.1
  · exact sixVertexDisagreementDart_local_card_eq_two hdegree d.1
  · exact retie.compatibleP
  · exact retie.compatibleQ
  · have hd := sixVertexDisagreementDart_side_mem d.1
    rw [mem_sixVertexLocalDisagreementSides] at hd
    exact bne_iff_ne.mpr hd
  · exact retie.partnerDisagrees

theorem orientedDisagreementDart_eq_of_vertex_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d e : SixVertexOrientedDisagreementDart omega eta)
    (hvertex : d.1.1.1 = e.1.1.1) : d = e := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hvertex
  · by_contra hside
    have hcard := sixVertexDisagreementDart_local_card_eq_two hdegree d.1
    have hdmem := sixVertexDisagreementDart_side_mem d.1
    have hemem : e.1.1.2 ∈ sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1) := by
      rw [hvertex]
      exact sixVertexDisagreementDart_side_mem e.1
    have hne := sixVertexLocalIncoming_ne_at_two_disagreements
      (sixVertexLocalIncomingPattern omega d.1.1.1)
      (sixVertexLocalIncomingPattern eta d.1.1.1)
      d.1.1.2 e.1.1.2
      (sixVertexLocalIncomingPattern_ice omega homega d.1.1.1)
      (sixVertexLocalIncomingPattern_ice eta heta d.1.1.1)
      hcard hdmem hemem (Ne.symm hside)
    apply hne
    rw [d.2]
    have he := e.2
    change sixVertexLocalIncomingPattern omega e.1.1.1 e.1.1.2 = true
      at he
    rwa [hvertex]

theorem exists_incoming_disagreement_side
    (p q : SixVertexLocalIncomingPattern)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2) :
    exists d : Fin 4, p d != q d /\ p d = true := by
  decide +revert

end StatMech.FrontierD
