/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part36
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

noncomputable def canonicalStableRawComponentResidualDirectPairEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (A : Finset (StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentReferenceSourceCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))) :
    (↑A ⊕ ↑A) ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let sourceMap := canonicalStableRawComponentReferenceSourceCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let directMap := canonicalStableRawComponentDirectEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let unused :=
    canonicalStableRawReferenceSourceDirectCollisionToUnusedDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : ↑A ⊕ ↑A → CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl collision => collision.1.1.1.1.2
    | Sum.inr collision => collision.1.1.2
  refine ⟨f, ?_⟩
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          change x.1.1.1.1.2 = y.1.1.1.1.2 at hxy
          have hfirst : x.1.1.1 = y.1.1.1 :=
            StatMech.FrontierA.crossCollision_snd_injective
              first directMap hxy
          have hresidual : x.1 = y.1 :=
            StatMech.FrontierA.crossCollision_fst_injective
              sourceMap directMap hfirst
          exact congrArg Sum.inl (Subtype.ext hresidual)
      | inr y =>
          exfalso
          change x.1.1.1.1.2 = y.1.1.2 at hxy
          exact (unused y.1).2 x.1.1.1 hxy.symm
  | inr x =>
      cases y with
      | inl y =>
          exfalso
          change x.1.1.2 = y.1.1.1.1.2 at hxy
          exact (unused x.1).2 y.1.1.1 hxy
      | inr y =>
          change x.1.1.2 = y.1.1.2 at hxy
          have hresidual : x.1 = y.1 :=
            StatMech.FrontierA.crossCollision_snd_injective
              sourceMap directMap hxy
          exact congrArg Sum.inr (Subtype.ext hresidual)


end StatMech.GrahamGHS.FourColor
