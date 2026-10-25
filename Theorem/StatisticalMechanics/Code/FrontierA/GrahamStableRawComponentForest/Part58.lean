/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part59
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


attribute [instance]
  FiniteRelationMinimalTightProblem.stateFintype
  FiniteRelationMinimalTightProblem.stateDecidableEq
  FiniteRelationMinimalTightProblem.tokenFintype
  FiniteRelationMinimalTightProblem.tokenDecidableEq

theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasOldOutputCrossing.naturalEscape_or_stableSelf_or_advancingRankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasOldOutputCrossing) :
    block.HasNaturalTokenEscape ∨
      block.HasStableSelfOldOutput ∨
      block.HasAdvancingOldOutputRankDrop := by
  obtain ⟨source, token, index, oldIndex, hincident, hsource, htoken,
      u, hu, htarget, hkind⟩ := hcross
  let natural := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component source
  by_cases hnaturalMem : natural ∈
      finiteEmbeddingBlock block.size block.tokenBlock
  · obtain ⟨q, _hq, hq⟩ := Finset.mem_map.mp hnaturalMem
    by_cases hqIndex : q = index
    · subst q
      have hnatural : natural = block.tokenBlock index := hq.symm
      have htargetNatural : u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p natural.1 := by
        rw [hnatural]
        simpa only [htoken] using htarget
      have hself : source.1.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p source.1.source := by
        by_contra hdirect
        rcases hkind with hstable | hadvancing
        · have huSource :=
            canonicalStableRawOwnerStableOutput_eq_of_directNaturalTarget
              source hdirect u htargetNatural hstable
          apply hsource oldIndex
          apply Subtype.ext
          change source.1 = (block.directs oldIndex).1
          exact huSource.symm.trans hu
        · exact
            canonicalStableRawOwnerAdvancingOutput_false_of_directNaturalTarget
              source hdirect u htargetNatural hadvancing
      rcases hkind with hstable | hadvancing
      · right
        left
        exact ⟨source, index, oldIndex, hsource,
          by simpa only [htoken] using hincident, hnatural, hself,
          u, hu, by simpa only [htoken] using htarget, hstable⟩
      · right
        right
        let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
          ⟨canonicalStableRawPreferredRightBase
              ends m j k l zero hloop hjk hkl hk0 p source.1.target,
            canonicalStableRawPreferredRightBase_mem
              ends m j k l zero hloop hjk hkl hk0 p source.1.target⟩
        have hownerRank : canonicalStableRawSourceRank
              ends m j k l zero p owner <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source :=
          canonicalStableRawPreferredRightBase_rank_lt_of_self
            ends m j k l zero hloop hjk hkl hk0 p source.1.target
              source.1.source hself.symm source.1.exceptional
        have huSource : u.source = owner := by
          apply Subtype.ext
          exact hadvancing
        exact ⟨source, index, oldIndex, hsource,
          by simpa only [htoken] using hincident, hnatural, u, hu,
          by simpa only [htoken] using htarget, hadvancing,
          huSource ▸ hownerRank⟩
    · left
      exact ⟨source, index, hsource,
        by simpa only [htoken] using hincident,
        Or.inr ⟨q, hqIndex, hq.symm⟩⟩
  · left
    exact ⟨source, index, hsource,
      by simpa only [htoken] using hincident, Or.inl hnaturalMem⟩


theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasStableSelfOldOutput.terminal_or_rankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hstable : block.HasStableSelfOldOutput) :
    Nonempty (CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source := by
  obtain ⟨source, index, _oldIndex, _hsource, _hcrossing, hnatural,
      hself, _u, _hu, _htarget, _houtputStable⟩ := hstable
  let self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨source.1, source.2, hself⟩
  have hraw := congrArg Subtype.val hnatural
  change canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno source.1 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno
        (block.directs index).1 at hraw
  unfold canonicalStableRawStateLeftToken at hraw
  rw [dif_pos hself, dif_neg (block.directs index).2.2] at hraw
  rcases canonicalStableRawSelfReroute_eq_directToken_dichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno
        source.1 (block.directs index).1 hself
          (block.directs index).2.2 hraw with
    ⟨_hdirectNext, hownerStable⟩ |
      ⟨hownerAdvancing, _hsourceEq, _htargetEq, _hne⟩
  · left
    let successor := canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component source
    have hnonexceptional : ¬ CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p successor.1 := by
      exact canonicalStableRawComponentSuccessorToken_not_exceptional_of_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno component
          self hownerStable
    exact ⟨⟨successor, hnonexceptional⟩⟩
  · right
    let hexceptional :=
      canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component
          self hownerAdvancing
    let direct := canonicalStableRawComponentExceptionalSuccessorDirect
      ends m j k l zero hloop hjk hkl hk0 p hno component
        source hexceptional
    refine ⟨source, direct.1, direct.2.1, ?_⟩
    exact
      canonicalStableRawComponentExceptionalSuccessorDirect_rank_lt_of_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component
          self hownerAdvancing


end StatMech.GrahamGHS.FourColor
