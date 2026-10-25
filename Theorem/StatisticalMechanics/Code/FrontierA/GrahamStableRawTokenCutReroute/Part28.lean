/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part27
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawComponentSecondCollisionAlternateToken_ne_occupant
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
    canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 := by
  intro h
  apply canonicalStableRawDirectAlternateLeftToken_ne_natural
    ends m j k l zero hloop hjk hkl hk0 p hno
      collision.1.2.1 collision.1.2.2.2
  have h' := congrArg Subtype.val h
  simpa only [canonicalStableRawComponentSecondCollisionAlternateToken,
    canonicalStableRawComponentDirectEmbedding_apply] using h'

theorem canonicalStableRawComponentSecondCollisionAlternateToken_ne_first
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
    canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 := by
  intro h
  apply canonicalStableRawComponentSecondCollisionAlternateToken_ne_occupant
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  exact h.trans collision.2


theorem canonicalStableRawComponentSecondCollisionAlternateToken_merge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (x y : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hxy : canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component x =
      canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component y) :
    x.1.2.1 = y.1.2.1 ∨
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p x.1.2.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p x.1.2.1 u := by
  let token := canonicalStableRawDirectAlternateLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno x.1.2.1 x.1.2.2.2
  have hxInc : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token x.1.2.1 :=
    (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p token x.1.2.1).2
        (canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
          ends m j k l zero hloop hjk hkl hk0 p hno x.1.2.1 x.1.2.2.2)
  have hyInc : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token y.1.2.1 := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p token y.1.2.1).2
    have hy := canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno y.1.2.1 y.1.2.2.2
    have htoken := congrArg Subtype.val hxy
    change canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.2.1 x.1.2.2.2 =
      canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno y.1.2.1 y.1.2.2.2 at htoken
    change CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawDirectAlternateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno
            x.1.2.1 x.1.2.2.2) y.1.2.1
    rw [htoken]
    exact hy
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno token
        x.1.2.1 y.1.2.1 hxInc hyInc with heq | hstable | hadvancing
  · exact Or.inl heq
  · exact Or.inr ⟨hstable.choose, Or.inl hstable.choose_spec.2.1⟩
  · exact Or.inr ⟨hadvancing.choose, Or.inr hadvancing.choose_spec.2.1⟩


theorem canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy
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
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentSecondCollisionAlternateToken
            ends m j k l zero hloop hjk hkl hk0 p hno component
              collision).1 ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  let token := canonicalStableRawDirectAlternateLeftToken
    ends m j k l zero hloop hjk hkl hk0 p hno
      collision.1.2.1 collision.1.2.2.2
  have hincidence : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token collision.1.2.1 :=
    canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.2.1 collision.1.2.2.2
  obtain ⟨u, huTarget, huKind, huComponent⟩ :=
    canonicalStableRawStateTokenIncidence_outputDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno token
        collision.1.2.1 hincidence
  refine ⟨u, huTarget, huKind, ?_⟩
  exact huComponent.trans collision.1.2.2.1


end StatMech.GrahamGHS.FourColor
