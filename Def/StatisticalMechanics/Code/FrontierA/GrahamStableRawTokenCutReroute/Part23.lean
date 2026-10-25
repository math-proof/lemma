/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyCutParity.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part23
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let f : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) ->
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := fun x =>
    ⟨canonicalStableRawReferenceOwnerLeftToken
        ends m j k l zero hloop hjk hkl hk0 p x.1.1.1 x.1.1.2.2,
      (canonicalStableRawReferenceOwnerLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno
          x.1.1.1 x.1.1.2.2).trans x.1.1.2.1⟩
  refine ⟨f, ?_⟩
  intro x y hxy
  apply StatMech.FrontierA.crossCollision_fst_injective
  apply Subtype.ext
  apply canonicalStableRawReferenceOwnerLeftToken_eq_imp
    ends m j k l zero hloop hjk hkl hk0 p
      x.1.1.1 y.1.1.1 x.1.1.2.2 y.1.1.2.2
  exact congrArg Subtype.val hxy

end StatMech.GrahamGHS.FourColor
