/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part5


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoCanonicalExpandedActiveReturnState_eq_output
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle layer x =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedSourceReturnState homega heta
          hdegree layer
          (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
            middle homegaSector hetaSector hmiddle layer x)) := by
  rfl

theorem sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedSourceReturnState homega heta
          hdegree layer x) := by
  rw [sixVertexDegreeTwoCanonicalExpandedActiveReturnState_eq_output,
    sixVertexDegreeTwoCanonicalExpandedInputState_self]

theorem sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_false_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightHead := cut.cutRight.head hright
    let rightPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
    let leftHead := cut.cutLeft.head hleft
    let leftPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false rightPredecessor) =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle false rightHead ∧
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false leftPredecessor) =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle false leftHead := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightHead := cut.cutRight.head hright
  let rightPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
  let leftHead := cut.cutLeft.head hleft
  let leftPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
  have hrightReturn : doubledAlignedFirstReturnPerm homega heta hdegree
      rightPredecessor = rightHead := by
    simp [rightPredecessor]
  have hleftReturn : doubledAlignedFirstReturnPerm homega heta hdegree
      leftPredecessor = leftHead := by
    simp [leftPredecessor]
  constructor
  · rw [sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input]
    simpa [sixVertexDegreeTwoCanonicalExpandedSourceReturnState,
      hrightReturn]
  · rw [sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input]
    simpa [sixVertexDegreeTwoCanonicalExpandedSourceReturnState,
      hleftReturn]

theorem sixVertexDegreeTwoCanonicalExpandedOutputState_coincident_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft))
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (cut.cutLeft.head hleft) =
      doubledAlignedBranchSwap
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer
          (cut.cutRight.head hright)) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  have hbranch :=
    canonicalDoubledAlignedCut_leftHead_eq_branchSwap_rightHead_of_vertex_eq
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
      hvertex
  change cut.cutLeft.head hleft =
      doubledAlignedBranchSwap (cut.cutRight.head hright) at hbranch
  change sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
      middle homegaSector hetaSector hmiddle layer (cut.cutLeft.head hleft) =
    doubledAlignedBranchSwap
      (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
        middle homegaSector hetaSector hmiddle layer
        (cut.cutRight.head hright))
  rw [hbranch,
    sixVertexDegreeTwoCanonicalExpandedOutputState_branchSwap]

theorem sixVertexDegreeTwoCanonicalExpandedActiveReturnState_coincident_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
      (cut.cutRight.head hright)
    let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
      (cut.cutLeft.head hleft)
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false leftPredecessor) =
      doubledAlignedBranchSwap
        (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta
          hdegree middle homegaSector hetaSector hmiddle false
          (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
            middle homegaSector hetaSector hmiddle false
            rightPredecessor)) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
    (cut.cutRight.head hright)
  let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
    (cut.cutLeft.head hleft)
  have hreturns :=
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_false_endpoints
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have houtputs :=
    sixVertexDegreeTwoCanonicalExpandedOutputState_coincident_endpoints homega
      heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex
      false
  exact hreturns.2.trans (houtputs.trans (congrArg doubledAlignedBranchSwap
    hreturns.1.symm))


theorem sixVertexDegreeTwoCanonicalExpanded_firstReturn_slot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer)
        ((finiteFirstReturn
          (fkMedialBlackBoundaryPerm
            (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta
              hdegree middle homegaSector hetaSector hmiddle layer))
          (activeBlackDart (omega := omega) (eta := eta))
          ⟨dart, hactive⟩).1) =
      (doubledAlignedVertex
          (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta
            hdegree middle homegaSector hetaSector hmiddle layer x),
        doubledAlignedSlot homega heta hdegree layer
          (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta
            hdegree middle homegaSector hetaSector hmiddle layer x)) := by
  let sourcePairing := alignedRoutingLoopPairing homega heta hdegree layer
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
    middle homegaSector hetaSector hmiddle layer
  let targetPairing := sixVertexDegreeTwoCanonicalExpandedTargetPairing
    homega heta hdegree middle homegaSector hetaSector hmiddle layer
  let input := sixVertexDegreeTwoCanonicalExpandedInputState homega heta
    hdegree middle homegaSector hetaSector hmiddle layer x
  let returned := sixVertexDegreeTwoCanonicalExpandedSourceReturnState homega
    heta hdegree layer input
  let swapped := fkMedialBlackDartMaskSwap mask dart
  have hpairing : targetPairing =
      fkMedialTogglePairingMask sourcePairing mask := by
    exact sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask
      homega heta hdegree middle homegaSector hetaSector hmiddle layer
  have hdart : dart =
      (fkColoredBlackDartStrandSlotEquiv targetPairing).symm
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) := by
    apply (fkColoredBlackDartStrandSlotEquiv targetPairing).injective
    simpa [targetPairing] using hslot
  have hswapped : swapped =
      doubledAlignedBlackDart homega heta hdegree layer input := by
    dsimp only [swapped]
    rw [hdart, hpairing]
    exact fkMedialBlackDartMaskSwap_canonicalTargetState homega heta hdegree
      mask layer x
  have hswappedActive :
      activeBlackDart (omega := omega) (eta := eta) swapped :=
    (activeBlackDart_maskSwap_iff mask dart).mpr hactive
  have hstart :
      (⟨swapped, hswappedActive⟩ : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d}) =
      doubledAlignedBlackDartEquiv homega heta hdegree layer input := by
    apply Subtype.ext
    exact hswapped
  have hsourceReturn :
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, hswappedActive⟩).1 =
      doubledAlignedBlackDart homega heta hdegree layer returned := by
    rw [hstart]
    cases layer
    · exact congrArg Subtype.val
        (doubledAlignedFirstReturnPerm_false_arrival homega heta hdegree input).symm
    · exact congrArg Subtype.val
        (sixVertexDegreeTwoAlignedTrueFirstReturn_arrival homega heta hdegree
          input)
  have htargetReturn := sixVertexDegreeTwoCanonicalExpanded_firstReturn_active
    homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
    hactive
  change (finiteFirstReturn
      (fkMedialBlackBoundaryPerm targetPairing)
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨dart, hactive⟩).1 =
    (finiteFirstReturn
      (alignedBoundaryPerm homega heta hdegree layer)
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨swapped, hswappedActive⟩).1 at htargetReturn
  change fkColoredBlackDartStrandSlotEquiv targetPairing
      ((finiteFirstReturn
        (fkMedialBlackBoundaryPerm targetPairing)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨dart, hactive⟩).1) = _
  rw [htargetReturn, hsourceReturn, hpairing,
    fkColoredBlackDartStrandSlotEquiv_togglePairingMask]
  simp only [Equiv.trans_apply]
  have hcoordinate :
      fkColoredBlackDartStrandSlotEquiv sourcePairing
          (doubledAlignedBlackDart homega heta hdegree layer returned) =
        (doubledAlignedVertex returned,
          doubledAlignedSlot homega heta hdegree layer returned) := by
    exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _
  rw [hcoordinate]
  rw [fkColoredParityMaskStrandSlotSwap_doubledAlignedState]
  rfl


end
end StatMech.FrontierD
