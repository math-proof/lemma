/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part28
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalStableRawComponentSecondCollisionAlternateFiber_outputBlock
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hcollision : collision ∈
      canonicalStableRawComponentSecondCollisionAlternateFiber
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor) :
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u.target = canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentSecondCollisionAlternateToken
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  have htoken : canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component collision =
      canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor :=
    by
      simpa only [canonicalStableRawComponentSecondCollisionAlternateFiber,
        Finset.mem_filter, Finset.mem_univ, true_and] using hcollision
  obtain ⟨u, huTarget, huKind, huComponent⟩ :=
    canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
  refine ⟨u, ?_, huKind, huComponent⟩
  exact huTarget.trans (congrArg
    (canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p)
    (congrArg Subtype.val htoken))


theorem canonicalStableRawComponentSecondCollisionAlternateFiber_source_or_owner
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (anchor collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hcollision : collision ∈
      canonicalStableRawComponentSecondCollisionAlternateFiber
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor) :
    let direct := collision.1.2
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
      ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p direct.1.target,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p direct.1.target⟩
    (next.target.1 = canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p direct.1.source ∧
        owner =
          (canonicalStableRawComponentSecondCollisionAlternateToken
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1.1) ∨
      (next.target.1 ≠ canonicalStableRawSelfBase
          ends m j k l zero hloop hjk hkl hk0 p direct.1.source ∧
        direct.1.source =
          (canonicalStableRawComponentSecondCollisionAlternateToken
            ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1.1) := by
  classical
  dsimp only
  have htoken : canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component collision =
      canonicalStableRawComponentSecondCollisionAlternateToken
        ends m j k l zero hloop hjk hkl hk0 p hno component anchor := by
    simpa only [canonicalStableRawComponentSecondCollisionAlternateFiber,
      Finset.mem_filter, Finset.mem_univ, true_and] using hcollision
  have hsource := congrArg
    (fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component => token.1.1)
    htoken
  rcases canonicalStableRawDirectAlternateLeftToken_source_split
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.2.1 collision.1.2.2.2 with howner | hdirect
  · exact Or.inl ⟨howner.1, howner.2.symm.trans hsource⟩
  · exact Or.inr ⟨hdirect.1, hdirect.2.symm.trans hsource⟩


end StatMech.GrahamGHS.FourColor
