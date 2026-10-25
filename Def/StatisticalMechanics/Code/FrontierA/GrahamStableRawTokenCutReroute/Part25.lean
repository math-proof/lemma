/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part25
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalStableRawReferenceSourceSelfCollisionToDirectEmbedding
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
      StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceSourceCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let selfMap := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : StatMech.FrontierA.crossCollision sourceMap selfMap ->
      StatMech.FrontierA.crossCollision sourceMap directMap := fun collision => by
    have hforce :=
      canonicalStableRawComponentReferenceSource_selfCollision_forces_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision.1.1 collision.1.2 collision.2
    have hselfState : collision.1.2 = collision.1.1.1.1.1.1 := by
      apply Subtype.ext
      exact hforce.1
    exact ⟨(collision.1.1, collision.1.1.1.1.1.2),
      collision.2.trans ((congrArg selfMap hselfState).trans
        collision.1.1.1.1.2)⟩
  refine ⟨f, ?_⟩
  intro x y hxy
  apply StatMech.FrontierA.crossCollision_fst_injective
  change f x = f y at hxy
  exact congrArg (fun collision : StatMech.FrontierA.crossCollision
    sourceMap directMap => collision.1.1) hxy


end StatMech.GrahamGHS.FourColor
