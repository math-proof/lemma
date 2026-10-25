/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part27
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def
    canonicalStableRawReferenceSourceSelfCollisionToUnusedDirectEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      {direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component //
        ∀ old : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          direct ≠ old.1.2} :=
  (canonicalStableRawReferenceSourceSelfCollisionToDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component).trans
    (canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component)


noncomputable def canonicalStableRawComponentSecondCollisionAlternateToken
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
    CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
  ⟨canonicalStableRawDirectAlternateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.2.1 collision.1.2.2.2,
    (canonicalStableRawDirectAlternateLeftToken_fullComponent
      ends m j k l zero hloop hjk hkl hk0 p hno
        collision.1.2.1 collision.1.2.2.2).trans collision.1.2.2.1⟩


end StatMech.GrahamGHS.FourColor
