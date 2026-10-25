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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle layer) := by
  intro first second heq
  apply (Fintype.equivFin
    (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
      middle homegaSector hetaSector hmiddle)).symm.injective
  apply Subtype.ext
  unfold sixVertexDegreeTwoBranchClosedBoundaryFinKey at heq
  cases layer
  · exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)).injective heq
  · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)).injective heq

theorem sixVertexDegreeTwoBranchClosedBoundaryFinKey_exists_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T) :
    (exists i, sixVertexDegreeTwoBranchClosedBoundaryFinKey
        homega heta hdegree middle homegaSector hetaSector hmiddle layer i =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree layer dart) ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    let occurrence : SixVertexDegreeTwoBranchClosedBoundaryOccurrence
        homega heta hdegree middle homegaSector hetaSector hmiddle :=
      (Fintype.equivFin
        (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle)).symm i
    have hdart : occurrence.1 = dart := by
      cases layer
      · exact (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)).injective hi
      · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
        exact (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)).injective hi
    rw [← hdart]
    exact occurrence.2
  · intro hdart
    let occurrence : SixVertexDegreeTwoBranchClosedBoundaryOccurrence
        homega heta hdegree middle homegaSector hetaSector hmiddle :=
      ⟨dart, hdart⟩
    let i := Fintype.equivFin
      (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
        middle homegaSector hetaSector hmiddle) occurrence
    refine ⟨i, ?_⟩
    unfold sixVertexDegreeTwoBranchClosedBoundaryFinKey
    congr 2
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)

theorem sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
      (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
          homega heta hdegree middle homegaSector hetaSector hmiddle)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree (!layer) dart) := by
  classical
  let occurrence : SixVertexDegreeTwoBranchClosedBoundaryOccurrence
      homega heta hdegree middle homegaSector hetaSector hmiddle :=
    ⟨dart, hdart⟩
  let i := Fintype.equivFin
    (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
      middle homegaSector hetaSector hmiddle) occurrence
  have hkey (currentLayer : Bool) :
      sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle
          homegaSector hetaSector hmiddle currentLayer i =
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree currentLayer dart := by
    unfold sixVertexDegreeTwoBranchClosedBoundaryFinKey
    congr 2
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)
  rw [← hkey layer, fkIndexedOccurrenceSlotEquiv_apply_key, hkey]

theorem sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart_of_not_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false
      (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
          homega heta hdegree middle homegaSector hetaSector hmiddle)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree layer dart) := by
  apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
  intro hexists
  exact hdart ((sixVertexDegreeTwoBranchClosedBoundaryFinKey_exists_iff
    homega heta hdegree middle homegaSector hetaSector hmiddle layer dart).mp
      hexists)


theorem sixVertexDegreeTwoBranchClosedBoundarySegments_branchSwap_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    doubledAlignedBlackDart homega heta hdegree false
        (doubledAlignedBranchSwap x) ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
            homegaSector hetaSector hmiddle) ↔
      doubledAlignedBlackDart homega heta hdegree false x ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
            homegaSector hetaSector hmiddle) := by
  rw [doubledAlignedBlackDart_mem_boundarySegments_iff,
    doubledAlignedBlackDart_mem_boundarySegments_iff]
  exact sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff
    homega heta hdegree middle homegaSector hetaSector hmiddle x


end
end StatMech.FrontierD
