/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hpreferredSelf : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p s.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p s.target⟩)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s
    next.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
            hloop hjk hkl hk0 p next.target,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p next.target⟩ := by
  dsimp only
  intro hnextSelf
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno s
  let oldOwner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  let nextOwner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p next.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p next.target⟩
  have howner : nextOwner = oldOwner := by
    apply Subtype.ext
    exact hstable.2
  apply canonicalStableRawExceptionalEdgeNext_target_ne
    ends m j k l zero hloop hjk hkl hk0 p hno s
  calc
    next.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p nextOwner := hnextSelf
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
          oldOwner := by rw [howner]
    _ = s.target.1 := hpreferredSelf.symm

theorem canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p) :
    CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno s ∨
      CanonicalStableRawOwnerStableStep
        ends m j k l zero hloop hjk hkl hk0 p hno s := by
  rcases canonicalStableRawExceptionalEdgeNext_source_or_owner_stable
      ends m j k l zero hloop hjk hkl hk0 p hno s with hadvance | hstable
  · exact Or.inl (congrArg Subtype.val hadvance)
  · exact Or.inr hstable


theorem canonicalStableRawOwnerAdvancingStep_rank_lt_of_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno s) :
    canonicalStableRawSourceRank ends m j k l zero p
        (canonicalStableRawExceptionalEdgeNext
          ends m j k l zero hloop hjk hkl hk0 p hno s).source <
      canonicalStableRawSourceRank ends m j k l zero p s.source := by
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p s.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p s.target⟩
  have hownerRank := canonicalStableRawPreferredRightBase_rank_lt_of_self
    ends m j k l zero hloop hjk hkl hk0 p s.target s.source hself.symm
      s.exceptional
  have hnextSource : (canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno s).source = owner := by
    apply Subtype.ext
    exact hadvancing
  rw [hnextSource]
  exact hownerRank


theorem canonicalStableRawExceptionalEdgeNext_nonself_of_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (s : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (hself : s.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.source) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno
    (next s).target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p (next s).source := by
  classical
  dsimp only
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno
  have htargetNe := canonicalStableRawExceptionalEdgeNext_target_ne
    ends m j k l zero hloop hjk hkl hk0 p hno s
  rcases canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable
      ends m j k l zero hloop hjk hkl hk0 p hno s with
    hadvancing | hstable
  · let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p s.target,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p s.target⟩
    have hnextSource : (next s).source = owner := by
      apply Subtype.ext
      exact hadvancing
    have hownerSelf : canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p owner = s.target.1 :=
      canonicalStableRawPreferredRightBase_self_eq_of_exists
        ends m j k l zero hloop hjk hkl hk0 p s.target
          ⟨s.source, hself.symm⟩
    intro hnextSelf
    apply htargetNe
    calc
      (next s).target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p (next s).source := hnextSelf
      _ = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p owner := by rw [hnextSource]
      _ = s.target.1 := hownerSelf
  · intro hnextSelf
    apply htargetNe
    calc
      (next s).target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p (next s).source := hnextSelf
      _ = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p s.source := by rw [hstable.1]
      _ = s.target.1 := hself.symm


end StatMech.GrahamGHS.FourColor
