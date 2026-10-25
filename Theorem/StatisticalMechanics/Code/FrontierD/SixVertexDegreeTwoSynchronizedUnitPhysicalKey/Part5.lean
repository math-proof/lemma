/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part4


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree x.1
    let sourcePairing := if layer then retie.pairingQ else retie.pairingP
    sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component layer (doubledAlignedVertex x) =
      if sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta
          hdegree component layer (doubledAlignedVertex x) then
        !sourcePairing
      else sourcePairing := by
  dsimp only
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega (doubledAlignedVertex x))
      (sixVertexLocalIncomingPattern eta (doubledAlignedVertex x))).card = 2 := by
    simpa [doubledAlignedVertex] using
      (sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1)
  let dart := orientedDisagreementDartAtActiveVertex homega heta
    (doubledAlignedVertex x) hactive
  have hdart : dart = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree dart x.1 rfl
  let retie := orientedDartAlignedRetie homega heta hdegree dart
  have hsource := alignedRoutingPairing_eq_at_active homega heta hdegree layer
    (doubledAlignedVertex x) hactive
  change alignedRoutingLoopPairing homega heta hdegree layer
      (doubledAlignedVertex x) =
    (if layer then retie.pairingQ else retie.pairingP) at hsource
  dsimp only [retie] at hsource
  rw [hdart] at hsource
  rw [sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing,
    fkMedialTogglePairingMask, hsource]


theorem sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component layer v =
      alignedRoutingLoopPairing homega heta hdegree layer v := by
  simp [sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing,
    sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive homega
      heta hdegree component layer v hzero, fkMedialTogglePairingMask]


@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_recover
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) :
    fkMedialTogglePairingMask
        (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
          heta hdegree component layer)
        (sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta
          hdegree component layer) =
      alignedRoutingLoopPairing homega heta hdegree layer := by
  exact fkMedialTogglePairingMask_self _ _


theorem sixVertexDegreeTwoSynchronizedComponentPhysicalTargetBoundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
          heta hdegree component layer) =
      (fkColoredParityMaskStrandSlotSwap
          (sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta
            hdegree component layer) false).trans
        ((fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer)).trans
          (fkColoredParityMaskStrandSlotSwap
            (sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega
              heta hdegree component layer) true)) := by
  exact fkColoredStrandSlotBoundaryPerm_togglePairingMask _ _


theorem sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
    let mask := sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega
      heta hdegree component layer
    let swapped := fkMedialBlackDartMaskSwap mask dart
    (finiteFirstReturn
        (fkMedialBlackBoundaryPerm
          (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
            heta hdegree component layer))
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨dart, hactive⟩).1 =
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
  classical
  let mask := sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega
    heta hdegree component layer
  have hreturn := finiteFirstReturn_togglePairingMask_active
    (alignedRoutingLoopPairing homega heta hdegree layer) mask
    (fun d hd => by
      have hzero := (hdegree d.1.1).resolve_right hd
      exact sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive
        homega heta hdegree component layer d.1.1 hzero) dart hactive
  simpa [sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing, mask]
    using hreturn


end
end StatMech.FrontierD
