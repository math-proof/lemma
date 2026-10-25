/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part25
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

theorem canonicalStableRawComponentReferenceOwnerEmbedding_ne_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (source target : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    canonicalStableRawComponentReferenceOwnerEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component source ≠
      canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component target := by
  classical
  intro heq
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p source.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p source.1.target⟩
  have hownerSelf : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p owner = source.1.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p source.1.target
        ⟨source.1.source, source.2.2.symm⟩
  have htoken : canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p source.1 source.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno target.1 := by
    have hraw := congrArg Subtype.val heq
    change (canonicalStableRawComponentAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨source.1, source.2.1⟩).1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno target.1 at hraw
    unfold canonicalStableRawComponentAlternateToken at hraw
    rw [dif_pos source.2.2] at hraw
    exact hraw
  have hsourceRaw := congrArg (fun token :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.1.1) htoken
  unfold canonicalStableRawReferenceOwnerLeftToken
    canonicalStableRawStateLeftToken at hsourceRaw
  rw [dif_pos target.2.2] at hsourceRaw
  change owner.1 = target.1.source.1 at hsourceRaw
  have hownerSource : owner = target.1.source := Subtype.ext hsourceRaw
  have htarget : target.1.target = source.1.target := by
    apply Subtype.ext
    calc
      target.1.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p target.1.source := target.2.2
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p owner := by rw [hownerSource]
      _ = source.1.target.1 := hownerSelf
  apply target.1.exceptional
  calc
    target.1.source.1 = owner.1 := congrArg Subtype.val hownerSource.symm
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p source.1.target := rfl
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p target.1.target := by rw [htarget]


end StatMech.GrahamGHS.FourColor
