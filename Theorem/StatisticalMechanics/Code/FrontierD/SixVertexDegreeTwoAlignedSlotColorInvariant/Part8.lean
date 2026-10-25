/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part8


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoAlignedFalseDartSlotSwap_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (mask : T.Vertex -> Bool) (parity layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree mask parity
        layer (doubledAlignedBlackDart homega heta hdegree false x) =
      if mask (doubledAlignedVertex x) &&
          (fkMedialVertexParity (doubledAlignedVertex x) == parity) then
        doubledAlignedBlackDart homega heta hdegree false
          (doubledAlignedBranchSwap x)
      else doubledAlignedBlackDart homega heta hdegree false x := by
  have hvertex :
      (doubledAlignedBlackDart homega heta hdegree false x).1.1 =
        doubledAlignedVertex x := by
    simp [doubledAlignedBlackDart, blackDartOfStrandSlot_vertex]
  rw [sixVertexDegreeTwoAlignedFalseDartSlotSwap, hvertex]
  split
  · cases layer
    · exact fkMedialBlackDartSwap_doubledAlignedBlackDart
        homega heta hdegree false x
    · rw [alignedBlackDartLayerSwap_active,
        fkMedialBlackDartSwap_doubledAlignedBlackDart]
      simpa using (congrArg
        (alignedBlackDartLayerSwap homega heta hdegree).symm
        (alignedBlackDartLayerSwap_active homega heta hdegree
          (doubledAlignedBranchSwap x))).symm
  · rfl


theorem sixVertexDegreeTwoBranchClosedFalseDartSlotSwap_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (parity layer : Bool)
    (dart : FKMedialBlackDart T) :
    sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree
          (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree
            middle homegaSector hetaSector hmiddle layer)
          parity layer dart ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
            homegaSector hetaSector hmiddle) ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  classical
  by_cases hactive : activeBlackDart (omega := omega) (eta := eta) dart
  · let active : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d} := ⟨dart, hactive⟩
    let x := (doubledAlignedBlackDartEquiv
      homega heta hdegree false).symm active
    have hdart : doubledAlignedBlackDart homega heta hdegree false x = dart :=
      congrArg Subtype.val ((doubledAlignedBlackDartEquiv
        homega heta hdegree false).apply_symm_apply active)
    rw [← hdart,
      sixVertexDegreeTwoAlignedFalseDartSlotSwap_active]
    split
    · rw [doubledAlignedBlackDart_mem_boundarySegments_iff,
        doubledAlignedBlackDart_mem_boundarySegments_iff]
      exact sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff
        homega heta hdegree middle homegaSector hetaSector hmiddle x
    · rfl
  · have hzero := (hdegree dart.1.1).resolve_right hactive
    have hmask := sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer
      dart.1.1 hzero
    simp [sixVertexDegreeTwoAlignedFalseDartSlotSwap, hmask]

theorem alignedBlackDartLayerSwap_vertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : FKMedialBlackDart T) :
    (alignedBlackDartLayerSwap homega heta hdegree dart).1.1 = dart.1.1 := by
  classical
  by_cases hactive : activeBlackDart (omega := omega) (eta := eta) dart
  · let active : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d} := ⟨dart, hactive⟩
    let x := (doubledAlignedBlackDartEquiv
      homega heta hdegree false).symm active
    have hdart : doubledAlignedBlackDart homega heta hdegree false x =
        dart := congrArg Subtype.val
      ((doubledAlignedBlackDartEquiv
        homega heta hdegree false).apply_symm_apply active)
    rw [← hdart, alignedBlackDartLayerSwap_active]
    simp [doubledAlignedBlackDart, blackDartOfStrandSlot_vertex,
      doubledAlignedVertex]
  · rw [alignedBlackDartLayerSwap_inactive
      homega heta hdegree dart hactive]

theorem alignedBlackDartLayerSwap_symm_vertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : FKMedialBlackDart T) :
    ((alignedBlackDartLayerSwap homega heta hdegree).symm dart).1.1 =
      dart.1.1 := by
  let swap := alignedBlackDartLayerSwap homega heta hdegree
  have h := alignedBlackDartLayerSwap_vertex homega heta hdegree
    (swap.symm dart)
  change (swap (swap.symm dart)).1.1 = (swap.symm dart).1.1 at h
  simpa using h.symm

theorem alignedBlackDartLayerSwap_symm_false_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree x.1
    (alignedBlackDartLayerSwap homega heta hdegree).symm
        (doubledAlignedBlackDart homega heta hdegree false x) =
      doubledAlignedBlackDart homega heta hdegree false
        (if retie.pairingP = retie.pairingQ then x
          else doubledAlignedBranchSwap x) := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  apply (alignedBlackDartLayerSwap homega heta hdegree).injective
  simp only [Equiv.apply_symm_apply]
  by_cases heq : retie.pairingP = retie.pairingQ
  · rw [if_pos heq, alignedBlackDartLayerSwap_active]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree x
    simpa [retie, heq] using hdart.symm
  · rw [if_neg heq, alignedBlackDartLayerSwap_active]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree (doubledAlignedBranchSwap x)
    simpa [retie, heq] using hdart.symm

@[simp] theorem sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_fst
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
      homega heta hdegree layer dart).1 = dart.1.1 := by
  cases layer
  · rfl
  · exact (congrArg Prod.fst
      (fkColoredBlackDartStrandSlotEquiv_apply
        (alignedRoutingLoopPairing homega heta hdegree true)
        (alignedBlackDartLayerSwap homega heta hdegree dart))).trans
      (alignedBlackDartLayerSwap_vertex homega heta hdegree dart)

theorem fkColoredParityMaskStrandSlotSwap_slotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (mask : T.Vertex -> Bool) (parity layer : Bool)
    (dart : FKMedialBlackDart T) :
    fkColoredParityMaskStrandSlotSwap mask parity
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer (sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree
          mask parity layer dart) := by
  by_cases hmask : mask dart.1.1 &&
      (fkMedialVertexParity dart.1.1 == parity)
  · cases layer
    · rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false,
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false]
      simp only [sixVertexDegreeTwoAlignedFalseDartSlotSwap, hmask, if_true,
        Bool.false_eq_true, if_false]
      rw [fkColoredBlackDartStrandSlot_blackSwap]
      simpa using fkColoredParityMaskStrandSlotSwap_apply_of_true
        mask parity
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree false dart) (by simpa using hmask)
    · let swap := alignedBlackDartLayerSwap homega heta hdegree
      rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true,
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true]
      simp only [sixVertexDegreeTwoAlignedFalseDartSlotSwap, hmask, if_true,
        Equiv.apply_symm_apply]
      rw [fkColoredBlackDartStrandSlot_blackSwap]
      have hselected :
          (mask (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
              homega heta hdegree true dart).1 &&
            (fkMedialVertexParity
              (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
                homega heta hdegree true dart).1 == parity)) = true := by
        rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_fst]
        exact hmask
      have hswap := fkColoredParityMaskStrandSlotSwap_apply_of_true
        mask parity
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree true dart) hselected
      rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_fst] at hswap
      simpa only [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true]
        using hswap
  · have hmaskFalse : (mask dart.1.1 &&
        (fkMedialVertexParity dart.1.1 == parity)) = false :=
      Bool.eq_false_of_not_eq_true hmask
    rw [sixVertexDegreeTwoAlignedFalseDartSlotSwap, if_neg hmask]
    have hunselected :
        (mask (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart).1 &&
          (fkMedialVertexParity
            (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
              homega heta hdegree layer dart).1 == parity)) = false := by
      rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_fst]
      exact hmaskFalse
    exact fkColoredParityMaskStrandSlotSwap_apply_of_false
      mask parity
      (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree layer dart) hunselected


end
end StatMech.FrontierD
