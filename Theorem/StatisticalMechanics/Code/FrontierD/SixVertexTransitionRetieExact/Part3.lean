/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTransitionRetieExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialUnitWindingSplitHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMedialCutAlignment.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLayeredCutBalance
import Def.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part2
open Equiv


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

theorem fkMedialLoopCount_retie_add_retie_eq_of_transitionTopology
    (source : Bool -> FKMedialLoopPairing T)
    (first second : T.Vertex)
    (htopology : FKMedialLayeredTransitionTopology source first second) :
    fkMedialLoopCount T
        (sixVertexRetieAtTransitionVertices (source false) first second) +
        fkMedialLoopCount T
          (sixVertexRetieAtTransitionVertices (source true) first second) =
      fkMedialLoopCount T (source false) +
        fkMedialLoopCount T (source true) := by
  rcases htopology with hcoincident | hdistinct
  · rcases hcoincident with ⟨hvertices, hopposite⟩
    rw [sixVertexRetieAtTransitionVertices_of_eq
        (source false) hvertices,
      sixVertexRetieAtTransitionVertices_of_eq
        (source true) hvertices]
    exact fkMedialLoopCount_toggle_add_toggle_eq_of_opposite
      (source false) (source true) first hopposite
  · rcases hdistinct with ⟨hvertices, hbalanced⟩
    have hne : first ≠ second := by
      simpa only [bne_iff_ne] using hvertices
    rw [sixVertexRetieAtTransitionVertices_of_ne (source false) hne,
      sixVertexRetieAtTransitionVertices_of_ne (source true) hne]
    have hfalse :=
      intCast_fkMedialLoopCount_twoToggle_sub_eq_splitScore
        (source false) first second
    have htrue :=
      intCast_fkMedialLoopCount_twoToggle_sub_eq_splitScore
        (source true) first second
    unfold FKMedialLayeredTwoCutBalanced at hbalanced
    omega


theorem sixVertexDegreeTwoAlignedTargetPairing_of_proper
    {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle
    sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
        homegaSector hetaSector hmiddle layer =
      sixVertexRetieAtTransitionVertices
        (alignedRoutingLoopPairing homega heta hdegree layer)
        (doubledAlignedVertex (cut.cutRight.head hright))
        (doubledAlignedVertex (cut.cutLeft.head hleft)) := by
  simp [sixVertexDegreeTwoAlignedTargetPairing, hleft, hright]


theorem sixVertexDegreeTwoAlignedTargetPairing_recover_of_proper
    {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle
    sixVertexRetieAtTransitionVertices
        (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
          homegaSector hetaSector hmiddle layer)
        (doubledAlignedVertex (cut.cutRight.head hright))
        (doubledAlignedVertex (cut.cutLeft.head hleft)) =
      alignedRoutingLoopPairing homega heta hdegree layer := by
  rw [sixVertexDegreeTwoAlignedTargetPairing_of_proper
    homega heta hdegree middle homegaSector hetaSector hmiddle
    hleft hright layer]
  exact sixVertexRetieAtTransitionVertices_self _ _ _


theorem sixVertexDegreeTwoAlignedTargetPairing_loopCount_eq_of_alternating
    {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool)
    (hvertices : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) ≠
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft))
    (halternating : FKMedialAlternatingTwoCut
      (alignedRoutingLoopPairing homega heta hdegree layer)
      (doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright))
      (doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft))) :
    fkMedialLoopCount T
        (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
          homegaSector hetaSector hmiddle layer) =
      fkMedialLoopCount T
        (alignedRoutingLoopPairing homega heta hdegree layer) := by
  rw [sixVertexDegreeTwoAlignedTargetPairing_of_proper
    homega heta hdegree middle homegaSector hetaSector hmiddle
    hleft hright layer]
  rw [sixVertexRetieAtTransitionVertices_of_ne _ hvertices]
  exact fkMedialLoopCount_twoToggle_eq_of_alternating _ _ _ halternating


theorem sixVertexDegreeTwoAlignedTargetPairing_totalLoopCount_eq_of_topology
    {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight ≠ [])
    (htopology : FKMedialLayeredTransitionTopology
      (alignedRoutingLoopPairing homega heta hdegree)
      (doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright))
      (doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft))) :
    fkMedialLoopCount T
        (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
          homegaSector hetaSector hmiddle false) +
        fkMedialLoopCount T
          (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
            homegaSector hetaSector hmiddle true) =
      fkMedialLoopCount T
          (alignedRoutingLoopPairing homega heta hdegree false) +
        fkMedialLoopCount T
          (alignedRoutingLoopPairing homega heta hdegree true) := by
  rw [sixVertexDegreeTwoAlignedTargetPairing_of_proper
      homega heta hdegree middle homegaSector hetaSector hmiddle
      hleft hright false,
    sixVertexDegreeTwoAlignedTargetPairing_of_proper
      homega heta hdegree middle homegaSector hetaSector hmiddle
      hleft hright true]
  exact fkMedialLoopCount_retie_add_retie_eq_of_transitionTopology
    (alignedRoutingLoopPairing homega heta hdegree) _ _ htopology


theorem doubledAlignedBoundarySegments_step_mem_iff_of_ne_cut_heads
    {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight ≠ [])
    (dart : FKMedialBlackDart T) (y : DoubledAlignedState omega eta)
    (hstep : alignedBoundaryPerm homega heta hdegree false dart =
      doubledAlignedBlackDart homega heta hdegree false y)
    (hneRight : y ≠ (canonicalDoubledAlignedOrbitChunkCut
      homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head
        hright)
    (hneLeft : y ≠ (canonicalDoubledAlignedOrbitChunkCut
      homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head
        hleft) :
    alignedBoundaryPerm homega heta hdegree false dart ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle) <->
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  have harrival :
      alignedBoundaryPerm homega heta hdegree false dart ∈
          doubledAlignedBoundarySegments homega heta hdegree false
            (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
              middle homegaSector hetaSector hmiddle) <->
        y ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
          middle homegaSector hetaSector hmiddle := by
    rw [hstep]
    exact doubledAlignedBlackDart_mem_boundarySegments_iff
      homega heta hdegree false _ y
  rw [harrival,
    mem_doubledAlignedBoundarySegments_predecessor_iff
      homega heta hdegree _ dart y hstep]
  exact cut.selected_predecessor_iff_of_ne_heads homega heta hdegree middle
    homegaSector hetaSector hmiddle hleft hright y hneRight hneLeft


theorem doubledAlignedBoundarySegments_rightHead_transition
    {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight ≠ [])
    (dart : FKMedialBlackDart T)
    (hstep : alignedBoundaryPerm homega heta hdegree false dart =
      doubledAlignedBlackDart homega heta hdegree false
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright)) :
    alignedBoundaryPerm homega heta hdegree false dart ∉
        doubledAlignedBoundarySegments homega heta hdegree false
          (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle) /\
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  have htransition := cut.rightHead_transition homega heta hdegree middle
    homegaSector hetaSector hmiddle hleft hright
  constructor
  · rw [hstep,
      doubledAlignedBlackDart_mem_boundarySegments_iff]
    exact htransition.1
  · rw [mem_doubledAlignedBoundarySegments_predecessor_iff
      homega heta hdegree _ dart (cut.cutRight.head hright) hstep]
    exact htransition.2


theorem doubledAlignedBoundarySegments_leftHead_transition
    {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight ≠ [])
    (dart : FKMedialBlackDart T)
    (hstep : alignedBoundaryPerm homega heta hdegree false dart =
      doubledAlignedBlackDart homega heta hdegree false
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
    alignedBoundaryPerm homega heta hdegree false dart ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle) /\
      dart ∉ doubledAlignedBoundarySegments homega heta hdegree false
        (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  have htransition := cut.leftHead_transition homega heta hdegree middle
    homegaSector hetaSector hmiddle hleft hright
  constructor
  · rw [hstep,
      doubledAlignedBlackDart_mem_boundarySegments_iff]
    exact htransition.1
  · rw [mem_doubledAlignedBoundarySegments_predecessor_iff
      homega heta hdegree _ dart (cut.cutLeft.head hleft) hstep]
    exact htransition.2


theorem canonicalDoubledAlignedCut_leftHead_eq_branchSwap_rightHead_of_vertex_eq
    {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
    (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
        homegaSector hetaSector hmiddle).cutLeft.head hleft =
      doubledAlignedBranchSwap
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  rcases doubledAlignedState_eq_or_branchSwap_of_vertex_eq
      homega heta hdegree (cut.cutRight.head hright)
        (cut.cutLeft.head hleft) hvertex with heq | heq
  · exact False.elim
      (cut.transition_states_ne homega heta hdegree middle homegaSector
        hetaSector hmiddle hleft hright heq.symm)
  · exact heq


theorem canonicalDoubledAlignedCut_coincident_oppositeSplits
    {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
    FKMedialCutSplits
        (alignedRoutingLoopPairing homega heta hdegree false)
        (doubledAlignedVertex
          ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
            homegaSector hetaSector hmiddle).cutRight.head hright)) <->
      Not (FKMedialCutSplits
        (alignedRoutingLoopPairing homega heta hdegree true)
        (doubledAlignedVertex
          ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
            homegaSector hetaSector hmiddle).cutRight.head hright))) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let right := cut.cutRight.head hright
  let left := cut.cutLeft.head hleft
  have hbranch : left = doubledAlignedBranchSwap right :=
    canonicalDoubledAlignedCut_leftHead_eq_branchSwap_rightHead_of_vertex_eq
      homega heta hdegree middle homegaSector hetaSector hmiddle
      hleft hright hvertex
  have hrightMem : right ∈ cut.cut := by
    rw [cut.cut_eq, List.mem_append]
    exact Or.inr (List.head_mem hright)
  have hleftMem : left ∈ cut.cut := by
    rw [cut.cut_eq, List.mem_append]
    exact Or.inl (List.head_mem hleft)
  have hstateCycle :
      (doubledAlignedFirstReturnPerm homega heta hdegree).SameCycle
        right left :=
    alignedPermOrderedAllOrbitLists_sameCycle_of_mem
      (doubledAlignedFirstReturnPerm homega heta hdegree) cut.cut
      (cut.cut_mem homega heta hdegree middle homegaSector hetaSector hmiddle)
      hrightMem hleftMem
  have hfalseCycle :=
    doubledAlignedFirstReturnPerm_sameCycle_falseBoundary
      homega heta hdegree hstateCycle
  have hfalseSplit : FKMedialCutSplits
      (alignedRoutingLoopPairing homega heta hdegree false)
      (doubledAlignedVertex right) := by
    have hcycle :
        (fkMedialBlackBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree false)).SameCycle
          (doubledAlignedBlackDart homega heta hdegree false right)
          (fkMedialBlackDartSwap
            (doubledAlignedBlackDart homega heta hdegree false right).1.1
            (doubledAlignedBlackDart homega heta hdegree false right)) := by
      rw [show (doubledAlignedBlackDart homega heta hdegree false right).1.1 =
          doubledAlignedVertex right by
        simp only [doubledAlignedBlackDart, blackDartOfStrandSlot_vertex],
        fkMedialBlackDartSwap_doubledAlignedBlackDart, ← hbranch]
      exact hfalseCycle
    have hsplit := (fkMedialCutSplits_iff_blackDartSwap_sameCycle
      (alignedRoutingLoopPairing homega heta hdegree false)
      (doubledAlignedBlackDart homega heta hdegree false right)).2 hcycle
    simpa only [doubledAlignedBlackDart, blackDartOfStrandSlot_vertex]
      using hsplit
  have hfalseDartColor :
      (sixVertexDegreeTwoAlignedColoredSource
          homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false right).1 =
        (sixVertexDegreeTwoAlignedColoredSource
          homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false left).1 := by
    obtain ⟨n, hn⟩ := hfalseCycle.exists_nat_pow_eq
    have hcolor :=
      (sixVertexDegreeTwoAlignedColoredSource
        homega heta hdegree false).color_blackBoundaryPerm_pow
        (doubledAlignedBlackDart homega heta hdegree false right) n
    change
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (((alignedBoundaryPerm homega heta hdegree false) ^ n)
            (doubledAlignedBlackDart homega heta hdegree false right)).1 =
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false right).1 at hcolor
    rw [hn] at hcolor
    exact hcolor.symm
  have hfalseSlotColor :
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, doubledAlignedVertex right,
            doubledAlignedSlot homega heta hdegree false right) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, doubledAlignedVertex (doubledAlignedBranchSwap right),
            doubledAlignedSlot homega heta hdegree false
              (doubledAlignedBranchSwap right)) := by
    rw [← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree false right,
      ← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree false (doubledAlignedBranchSwap right),
      ← hbranch]
    exact hfalseDartColor
  have htrueColorNe :=
    sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne_of_false_eq
      homega heta hdegree right hfalseSlotColor
  have htrueNotSplit : Not (FKMedialCutSplits
      (alignedRoutingLoopPairing homega heta hdegree true)
      (doubledAlignedVertex right)) := by
    intro hsplit
    have hsplit' : FKMedialCutSplits
        (alignedRoutingLoopPairing homega heta hdegree true)
        (doubledAlignedBlackDart homega heta hdegree true right).1.1 := by
      simpa only [doubledAlignedBlackDart, blackDartOfStrandSlot_vertex]
        using hsplit
    have htrueCycle :=
      (fkMedialCutSplits_iff_blackDartSwap_sameCycle
        (alignedRoutingLoopPairing homega heta hdegree true)
        (doubledAlignedBlackDart homega heta hdegree true right)).1 hsplit'
    rw [show (doubledAlignedBlackDart homega heta hdegree true right).1.1 =
        doubledAlignedVertex right by
      simp only [doubledAlignedBlackDart, blackDartOfStrandSlot_vertex]] at htrueCycle
    rw [fkMedialBlackDartSwap_doubledAlignedBlackDart] at htrueCycle
    change (alignedBoundaryPerm homega heta hdegree true).SameCycle
      (doubledAlignedBlackDart homega heta hdegree true right)
      (doubledAlignedBlackDart homega heta hdegree true
        (doubledAlignedBranchSwap right)) at htrueCycle
    obtain ⟨n, hn⟩ := htrueCycle.exists_nat_pow_eq
    have hcolor :=
      (sixVertexDegreeTwoAlignedColoredSource
        homega heta hdegree true).color_blackBoundaryPerm_pow
        (doubledAlignedBlackDart homega heta hdegree true right) n
    change
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree true).color
          (((alignedBoundaryPerm homega heta hdegree true) ^ n)
            (doubledAlignedBlackDart homega heta hdegree true right)).1 =
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree true).color
          (doubledAlignedBlackDart homega heta hdegree true right).1 at hcolor
    rw [hn] at hcolor
    apply (bne_iff_ne.mp htrueColorNe)
    rw [← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree true right,
      ← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree true (doubledAlignedBranchSwap right)]
    exact hcolor.symm
  constructor
  · intro _
    exact htrueNotSplit
  · intro _
    exact hfalseSplit

end
end StatMech.FrontierD
