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
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part26
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem CanonicalDoubledAlignedOrbitChunkCut.cut_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn) :
    cut.cut ∈ alignedPermOrderedAllOrbitLists
      (doubledAlignedFirstReturnPerm homega heta hdegree) := by
  rw [cut.orbitLists]
  simp

theorem CanonicalDoubledAlignedOrbitChunkCut.proper_boundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ []) :
    doubledAlignedFirstReturnPerm homega heta hdegree
        (cut.cutLeft.getLast hleft) =
      cut.cutRight.head hright :=
  alignedPermOrderedOrbitChunk_split_boundary
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    cut.cut cut.cutLeft cut.cutRight (cut.cut_mem)
    cut.cut_eq hleft hright

theorem CanonicalDoubledAlignedOrbitChunkCut.proper_entry_boundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ []) :
    doubledAlignedFirstReturnPerm homega heta hdegree
        (cut.cutRight.getLast hright) =
      cut.cutLeft.head hleft := by
  have hcut : cut.cut ≠ [] := by
    rw [cut.cut_eq]
    exact List.append_ne_nil_of_left_ne_nil hleft cut.cutRight
  have hcycle := alignedPermOrderedAllOrbitLists_getLast
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    cut.cut cut.cut_mem hcut
  have hlast : cut.cut.getLast hcut =
      cut.cutRight.getLast hright := by
    have happ : cut.cutLeft ++ cut.cutRight ≠ [] :=
      List.append_ne_nil_of_right_ne_nil cut.cutLeft hright
    exact (List.getLast_congr hcut happ cut.cut_eq).trans
      (List.getLast_append_of_right_ne_nil
        cut.cutLeft cut.cutRight hright)
  have hhead : cut.cut.head hcut = cut.cutLeft.head hleft := by
    have happ : cut.cutLeft ++ cut.cutRight ≠ [] :=
      List.append_ne_nil_of_left_ne_nil hleft cut.cutRight
    have hcongr : cut.cut.head hcut =
        (cut.cutLeft ++ cut.cutRight).head happ := by
      rw [List.head_eq_getElem, List.head_eq_getElem]
      exact getElem_congr cut.cut_eq rfl _
    exact hcongr.trans (List.head_append_of_ne_nil hleft)
  rw [hlast, hhead] at hcycle
  exact hcycle


theorem CanonicalDoubledAlignedOrbitChunkCut.transition_states_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ []) :
    cut.cutRight.head hright ≠ cut.cutLeft.head hleft := by
  have hchunkNodup := alignedPermOrderedAllOrbitLists_chunk_nodup
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    cut.cut cut.cut_mem
  have happNodup : (cut.cutLeft ++ cut.cutRight).Nodup := by
    simpa [cut.cut_eq] using hchunkNodup
  have hdisjoint : cut.cutLeft.Disjoint cut.cutRight := by
    rw [List.disjoint_left]
    intro a ha hb
    exact ((List.nodup_append.mp happNodup).2.2 a ha a hb) rfl
  intro heq
  apply (List.disjoint_left.mp hdisjoint) (List.head_mem hleft)
  rw [← heq]
  exact List.head_mem hright

theorem CanonicalDoubledAlignedOrbitChunkCut.selected_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ [])
    (x : DoubledAlignedState omega eta) :
    doubledAlignedFirstReturnPerm homega heta hdegree x ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn ↔
      (x ∈ canonicalDoubledAlignedSelectedStates
          homega heta hdegree n homegaSector hetaSector hn ∧
        x ≠ cut.cutLeft.getLast hleft) ∨
      x = cut.cutRight.getLast hright := by
  rw [cut.selected_eq]
  exact alignedPermOrderedOrbitPrefix_mem_iff
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    cut.before cut.cut cut.after cut.cutLeft cut.cutRight
    cut.orbitLists cut.cut_eq hleft hright x

theorem CanonicalDoubledAlignedOrbitChunkCut.not_selected_invariant
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ []) :
    ¬ forall x : DoubledAlignedState omega eta,
      (doubledAlignedFirstReturnPerm homega heta hdegree x ∈
          canonicalDoubledAlignedSelectedStates
            homega heta hdegree n homegaSector hetaSector hn ↔
        x ∈ canonicalDoubledAlignedSelectedStates
          homega heta hdegree n homegaSector hetaSector hn) := by
  intro hinvariant
  let x := cut.cutLeft.getLast hleft
  have hx : x ∈ canonicalDoubledAlignedSelectedStates
      homega heta hdegree n homegaSector hetaSector hn := by
    rw [cut.selected_eq, List.mem_append]
    exact Or.inr (List.getLast_mem hleft)
  have hchunkNodup := alignedPermOrderedAllOrbitLists_chunk_nodup
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    cut.cut cut.cut_mem
  have happNodup : (cut.cutLeft ++ cut.cutRight).Nodup := by
    simpa [cut.cut_eq] using hchunkNodup
  have hdisjoint : cut.cutLeft.Disjoint cut.cutRight := by
    rw [List.disjoint_left]
    intro a ha hb
    exact ((List.nodup_append.mp happNodup).2.2 a ha a hb) rfl
  have hne : x ≠ cut.cutRight.getLast hright := by
    intro heq
    apply (List.disjoint_left.mp hdisjoint) (List.getLast_mem hleft)
    have heq' : cut.cutLeft.getLast hleft =
        cut.cutRight.getLast hright := heq
    rw [heq']
    exact List.getLast_mem hright
  have hexit : doubledAlignedFirstReturnPerm homega heta hdegree x ∉
      canonicalDoubledAlignedSelectedStates
        homega heta hdegree n homegaSector hetaSector hn := by
    rw [CanonicalDoubledAlignedOrbitChunkCut.selected_mem_iff
      homega heta hdegree n homegaSector hetaSector hn
      cut hleft hright x]
    simp [x, hne]
  exact hexit ((hinvariant x).mpr hx)

theorem canonicalDoubledAlignedOrbitChunkCut_cases
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn
    cut.cutLeft = [] ∨ cut.cutRight = [] ∨
      (cut.cutLeft ≠ [] ∧ cut.cutRight ≠ []) := by
  dsimp
  by_cases hleft : (canonicalDoubledAlignedOrbitChunkCut
      homega heta hdegree n homegaSector hetaSector hn).cutLeft = []
  · exact Or.inl hleft
  · by_cases hright : (canonicalDoubledAlignedOrbitChunkCut
        homega heta hdegree n homegaSector hetaSector hn).cutRight = []
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr ⟨hleft, hright⟩)

end ScratchLocalRetieC
