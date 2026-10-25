/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part23
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


@[simp] theorem canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component x).1 =
      canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p x.1.1.1 x.1.1.2.2 := by
  rfl

theorem canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component x ≠
      canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self := by
  classical
  intro heq
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.target⟩
  have hownerSelf : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p owner = x.1.1.1.target.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p x.1.1.1.target
        ⟨x.1.1.1.source, x.1.1.2.2.symm⟩
  have htoken : canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p x.1.1.1 x.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno self.1 := by
    simpa only [canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
      canonicalStableRawComponentSelfEmbedding_apply] using congrArg Subtype.val heq
  have hsourceRaw := congrArg (fun token :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.1.1) htoken
  unfold canonicalStableRawReferenceOwnerLeftToken
    canonicalStableRawStateLeftToken at hsourceRaw
  rw [dif_pos self.2.2] at hsourceRaw
  change owner.1 = self.1.source.1 at hsourceRaw
  have hownerSource : owner = self.1.source := Subtype.ext hsourceRaw
  have htarget : self.1.target = x.1.1.1.target := by
    apply Subtype.ext
    calc
      self.1.target.1 = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p self.1.source := self.2.2
      _ = canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p owner := by rw [hownerSource]
      _ = x.1.1.1.target.1 := hownerSelf
  apply self.1.exceptional
  calc
    self.1.source.1 = owner.1 := congrArg Subtype.val hownerSource.symm
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p x.1.1.1.target := rfl
    _ = canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p self.1.target := by rw [htarget]


theorem canonicalStableRawComponentReferenceOwner_directOccupant_source
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    collision.1.2.1.source.1 =
      canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p collision.1.1.1.1.1.target := by
  have htoken : canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1.1.1 collision.1.1.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.2.1 := by
    simpa only [canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
      canonicalStableRawComponentDirectEmbedding_apply] using
        congrArg Subtype.val collision.2
  have hsource := congrArg (fun token :
    CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.1.1) htoken
  unfold canonicalStableRawReferenceOwnerLeftToken
    canonicalStableRawStateLeftToken at hsource
  rw [dif_neg collision.1.2.2.2] at hsource
  exact hsource.symm


end StatMech.GrahamGHS.FourColor
