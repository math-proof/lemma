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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part29
open StatMech.FrontierD


namespace StatMech.FrontierD

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

theorem CanonicalDoubledAlignedOrbitChunkCut.cutLeft_mem_selected
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
    {x : DoubledAlignedState omega eta} (hx : x ∈ cut.cutLeft) :
    x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
      homegaSector hetaSector hn := by
  rw [cut.selected_eq, List.mem_append]
  exact Or.inr hx

theorem CanonicalDoubledAlignedOrbitChunkCut.cutRight_not_mem_selected
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
    {x : DoubledAlignedState omega eta} (hx : x ∈ cut.cutRight) :
    x ∉ canonicalDoubledAlignedSelectedStates homega heta hdegree n
      homegaSector hetaSector hn := by
  let split := canonicalDoubledAlignedUnitOrbitSplit
    homega heta hdegree n homegaSector hetaSector hn
  have hall := alignedPermOrderedAllOrbits_nodup
    (doubledAlignedFirstReturnPerm homega heta hdegree)
  rw [split.split] at hall
  have hsecond : x ∈ split.second := by
    rw [cut.complement_eq, List.mem_append]
    exact Or.inl hx
  intro hselected
  exact (List.nodup_append.mp hall).2.2 x hselected x hsecond rfl

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

theorem CanonicalDoubledAlignedOrbitChunkCut.selected_predecessor_iff_of_ne_heads
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
    (y : DoubledAlignedState omega eta)
    (hneRight : y ≠ cut.cutRight.head hright)
    (hneLeft : y ≠ cut.cutLeft.head hleft) :
    y ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn ↔
      (doubledAlignedFirstReturnPerm
        homega heta hdegree).symm y ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn := by
  let sigma := doubledAlignedFirstReturnPerm homega heta hdegree
  let x := sigma.symm y
  have hxRight : x ≠ cut.cutRight.getLast hright := by
    intro hx
    apply hneLeft
    have hentry := cut.proper_entry_boundary
      homega heta hdegree n homegaSector hetaSector hn hleft hright
    change sigma (cut.cutRight.getLast hright) =
      cut.cutLeft.head hleft at hentry
    calc
      y = sigma x := by simp [x, sigma]
      _ = sigma (cut.cutRight.getLast hright) := by rw [hx]
      _ = cut.cutLeft.head hleft := hentry
  have hxLeft : x ≠ cut.cutLeft.getLast hleft := by
    intro hx
    apply hneRight
    have hboundary := cut.proper_boundary
      homega heta hdegree n homegaSector hetaSector hn hleft hright
    change sigma (cut.cutLeft.getLast hleft) =
      cut.cutRight.head hright at hboundary
    calc
      y = sigma x := by simp [x, sigma]
      _ = sigma (cut.cutLeft.getLast hleft) := by rw [hx]
      _ = cut.cutRight.head hright := hboundary
  have hiff := cut.selected_mem_iff homega heta hdegree n
    homegaSector hetaSector hn hleft hright x
  change y ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
        homegaSector hetaSector hn ↔
    x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
      homegaSector hetaSector hn
  rw [show y = sigma x by simp [x, sigma]]
  simpa [sigma, hxLeft, hxRight] using hiff


theorem CanonicalDoubledAlignedOrbitChunkCut.selected_invariant_of_left_empty
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
    (hleft : cut.cutLeft = [])
    (x : DoubledAlignedState omega eta) :
    doubledAlignedFirstReturnPerm homega heta hdegree x ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn <->
      x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
        homegaSector hetaSector hn := by
  rw [cut.selected_eq, hleft, List.append_nil]
  apply alignedPermOrderedAllOrbitLists_prefix_mem_iff
    (doubledAlignedFirstReturnPerm homega heta hdegree) cut.before
    (cut.cut :: cut.after)
  simpa using cut.orbitLists


theorem CanonicalDoubledAlignedOrbitChunkCut.selected_invariant_of_right_empty
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
    (hright : cut.cutRight = [])
    (x : DoubledAlignedState omega eta) :
    doubledAlignedFirstReturnPerm homega heta hdegree x ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn <->
      x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
        homegaSector hetaSector hn := by
  have hcut : cut.cut = cut.cutLeft := by
    simpa [hright] using cut.cut_eq
  rw [cut.selected_eq, ← hcut]
  have hinvariant := alignedPermOrderedAllOrbitLists_prefix_mem_iff
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    (cut.before ++ [cut.cut]) cut.after (by simpa using cut.orbitLists) x
  simpa [List.flatten_append] using hinvariant

theorem CanonicalDoubledAlignedOrbitChunkCut.rightHead_transition
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
    cut.cutRight.head hright ∉
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn ∧
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm
          (cut.cutRight.head hright) ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn := by
  constructor
  · exact cut.cutRight_not_mem_selected homega heta hdegree n
      homegaSector hetaSector hn (List.head_mem hright)
  · have hprev : (doubledAlignedFirstReturnPerm homega heta hdegree).symm
        (cut.cutRight.head hright) = cut.cutLeft.getLast hleft := by
      apply (doubledAlignedFirstReturnPerm homega heta hdegree).injective
      simp only [Equiv.apply_symm_apply]
      exact (cut.proper_boundary homega heta hdegree n homegaSector
        hetaSector hn hleft hright).symm
    rw [hprev]
    exact cut.cutLeft_mem_selected homega heta hdegree n
      homegaSector hetaSector hn (List.getLast_mem hleft)

theorem CanonicalDoubledAlignedOrbitChunkCut.leftHead_transition
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
    cut.cutLeft.head hleft ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn ∧
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm
          (cut.cutLeft.head hleft) ∉
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn := by
  constructor
  · exact cut.cutLeft_mem_selected homega heta hdegree n
      homegaSector hetaSector hn (List.head_mem hleft)
  · have hprev : (doubledAlignedFirstReturnPerm homega heta hdegree).symm
        (cut.cutLeft.head hleft) = cut.cutRight.getLast hright := by
      apply (doubledAlignedFirstReturnPerm homega heta hdegree).injective
      simp only [Equiv.apply_symm_apply]
      exact (cut.proper_entry_boundary homega heta hdegree n homegaSector
        hetaSector hn hleft hright).symm
    rw [hprev]
    exact cut.cutRight_not_mem_selected homega heta hdegree n
      homegaSector hetaSector hn (List.getLast_mem hright)

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


end StatMech.FrontierD
