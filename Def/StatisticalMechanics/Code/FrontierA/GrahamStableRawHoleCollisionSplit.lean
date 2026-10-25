/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute.Part33
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

noncomputable def canonicalStableRawLeftTokenKey
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (token : CanonicalStableRawLeftSurplusToken
      ends m j k l zero hloop hjk hkl hk0 p) :
    ↑(canonicalRawCommonClosure ends m j k l zero p) ×
      leftSourceMaskFiber ends m j k l zero p :=
  (token.1, token.2.1)


noncomputable def canonicalStableRawComponentTokenKeyEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      (↑(canonicalRawCommonClosure ends m j k l zero p) ×
        leftSourceMaskFiber ends m j k l zero p) := by
  classical
  let f : CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component →
      (↑(canonicalRawCommonClosure ends m j k l zero p) ×
        leftSourceMaskFiber ends m j k l zero p) :=
    fun token => canonicalStableRawLeftTokenKey
      ends m j k l zero hloop hjk hkl hk0 p token.1
  refine ⟨f, ?_⟩
  intro x y hxy
  apply Subtype.ext
  apply canonicalStableRawLeftSurplusToken_eq_of_source_target_eq
    ends m j k l zero hloop hjk hkl hk0 p
  · exact congrArg Prod.fst hxy
  · exact congrArg Prod.snd hxy


noncomputable def canonicalStableRawComponentDirectKeyEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      (↑(canonicalRawCommonClosure ends m j k l zero p) ×
        leftSourceMaskFiber ends m j k l zero p) :=
  (canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component).trans
      (canonicalStableRawComponentTokenKeyEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)


noncomputable def canonicalStableRawComponentReferenceOwnerKeyEmbedding
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
      (↑(canonicalRawCommonClosure ends m j k l zero p) ×
        leftSourceMaskFiber ends m j k l zero p) :=
  (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component).trans
      (canonicalStableRawComponentTokenKeyEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)


noncomputable def canonicalStableRawComponentReferenceSourceFirstKeyEmbedding
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
      (↑(canonicalRawCommonClosure ends m j k l zero p) ×
        leftSourceMaskFiber ends m j k l zero p) :=
  (canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component).trans
      (canonicalStableRawComponentTokenKeyEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)

end StatMech.GrahamGHS.FourColor
