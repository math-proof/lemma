/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part25
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawComponentReferenceSource_directCollision_source
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    collision.1.2.1.source = collision.1.1.1.1.1.1.1.source := by
  have htoken := congrArg Subtype.val collision.2
  have hsource := congrArg Sigma.fst htoken
  simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
    canonicalStableRawComponentDirectEmbedding_apply,
    canonicalStableRawReferenceSourceLeftToken_source,
    canonicalStableRawStateLeftToken, dif_neg collision.1.2.2.2] using
      hsource.symm


theorem canonicalStableRawComponentReferenceSource_directCollision_target
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    collision.1.2.1.target = collision.1.1.1.2.1.target := by
  apply Subtype.ext
  have hsourceToken : canonicalStableRawReferenceSourceLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1.1.1.1.1 collision.1.1.1.1.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.2.1 := by
    simpa only [canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply,
      canonicalStableRawComponentDirectEmbedding_apply] using
        congrArg Subtype.val collision.2
  have hsourceTarget := congrArg
    (fun token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.2.1) hsourceToken
  have hownerToken : canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1.1.1.1.1 collision.1.1.1.1.1.1.2.2 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1.2.1 := by
    simpa only [canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply,
      canonicalStableRawComponentDirectEmbedding_apply] using
        congrArg Subtype.val collision.1.1.2
  have hownerTarget := congrArg
    (fun token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p => token.2.1) hownerToken
  simp only [canonicalStableRawReferenceSourceLeftToken_target,
    canonicalStableRawReferenceOwnerLeftToken_target] at hsourceTarget hownerTarget
  unfold canonicalStableRawStateLeftToken at hsourceTarget hownerTarget
  rw [dif_neg collision.1.2.2.2] at hsourceTarget
  rw [dif_neg collision.1.1.1.2.2.2] at hownerTarget
  exact hsourceTarget.symm.trans hownerTarget


theorem canonicalStableRawComponentReferenceSource_directCollision_selfBase_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        collision.1.2.1.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1.2.1.source := by
  let s := collision.1.1.1.1.1.1.1
  have hz : collision.1.2.1.source = s.source :=
    canonicalStableRawComponentReferenceSource_directCollision_source
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have hd : collision.1.1.1.2.1.source =
      canonicalStableRawReferenceOwner
        ends m j k l zero hloop hjk hkl hk0 p s := by
    apply Subtype.ext
    exact canonicalStableRawComponentReferenceOwner_directOccupant_source
      ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1
  calc
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        collision.1.2.1.source =
      canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        s.source := congrArg _ hz
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawReferenceOwner
          ends m j k l zero hloop hjk hkl hk0 p s) :=
      canonicalStableRawReferenceOwner_sourceBase
        ends m j k l zero hloop hjk hkl hk0 p s
          collision.1.1.1.1.1.1.2.2
    _ = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1.2.1.source := congrArg _ hd.symm


theorem canonicalStableRawComponentReferenceSource_directCollision_threeSources
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ owner : ↑(canonicalRawCommonClosure ends m j k l zero p),
      collision.1.2.1.source ≠ collision.1.1.1.2.1.source ∧
        collision.1.2.1.source ≠ owner ∧
        collision.1.1.1.2.1.source ≠ owner ∧
        CanonicalRawGateRelated ends m j k l zero p
          collision.1.2.1.source.1 collision.1.2.1.target.1 ∧
        CanonicalRawGateRelated ends m j k l zero p
          collision.1.1.1.2.1.source.1 collision.1.2.1.target.1 ∧
        CanonicalRawGateRelated ends m j k l zero p
          owner.1 collision.1.2.1.target.1 := by
  let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p collision.1.2.1.target,
      canonicalStableRawPreferredRightBase_mem ends m j k l zero
        hloop hjk hkl hk0 p collision.1.2.1.target⟩
  have htarget :=
    canonicalStableRawComponentReferenceSource_directCollision_target
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have hsource :=
    canonicalStableRawComponentReferenceSource_directCollision_source
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have hfirstSecond : collision.1.2.1.source ≠
      collision.1.1.1.2.1.source := by
    intro heq
    apply collision.1.1.1.1.1.1.1.exceptional
    calc
      collision.1.1.1.1.1.1.1.source.1 =
          collision.1.2.1.source.1 := congrArg Subtype.val hsource.symm
      _ = collision.1.1.1.2.1.source.1 := congrArg Subtype.val heq
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p collision.1.1.1.1.1.1.1.target :=
        canonicalStableRawComponentReferenceOwner_directOccupant_source
          ends m j k l zero hloop hjk hkl hk0 p hno component
            collision.1.1
  have hfirstOwner : collision.1.2.1.source ≠ owner := by
    intro heq
    apply collision.1.2.1.exceptional
    exact congrArg Subtype.val heq
  have hsecondOwner : collision.1.1.1.2.1.source ≠ owner := by
    intro heq
    apply collision.1.1.1.2.1.exceptional
    rw [← htarget]
    exact congrArg Subtype.val heq
  refine ⟨owner, hfirstSecond, hfirstOwner, hsecondOwner,
    collision.1.2.1.related, ?_, ?_⟩
  · rw [htarget]
    exact collision.1.1.1.2.1.related
  · exact canonicalStableRawPreferredRightBase_related
      ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1.target


theorem canonicalStableRawComponentReferenceSource_directCollision_three_le_degree
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    let degree : Nat := by
      classical
      exact ((canonicalRawCommonClosure ends m j k l zero p).filter
        (fun c => CanonicalRawGateRelated ends m j k l zero p c
          collision.1.2.1.target.1)).card
    3 ≤ degree := by
  classical
  dsimp only
  obtain ⟨owner, h12, h1o, h2o, hrel1, hrel2, hrelo⟩ :=
    canonicalStableRawComponentReferenceSource_directCollision_threeSources
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have h12v : collision.1.2.1.source.1 ≠
      collision.1.1.1.2.1.source.1 := fun h => h12 (Subtype.ext h)
  have h1ov : collision.1.2.1.source.1 ≠ owner.1 :=
    fun h => h1o (Subtype.ext h)
  have h2ov : collision.1.1.1.2.1.source.1 ≠ owner.1 :=
    fun h => h2o (Subtype.ext h)
  let witnesses : Finset (leftSourceMaskFiber ends m j k l zero p) :=
    {collision.1.2.1.source.1, collision.1.1.1.2.1.source.1, owner.1}
  have hwitnesses : witnesses.card = 3 := by
    simp only [witnesses]
    simp [h12v, h1ov, h2ov]
  rw [← hwitnesses]
  apply Finset.card_le_card
  intro c hc
  simp only [witnesses, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl
  · exact Finset.mem_filter.mpr ⟨collision.1.2.1.source.2, hrel1⟩
  · exact Finset.mem_filter.mpr ⟨collision.1.1.1.2.1.source.2, hrel2⟩
  · exact Finset.mem_filter.mpr ⟨owner.2, hrelo⟩


end StatMech.GrahamGHS.FourColor
