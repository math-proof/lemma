/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part25
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

noncomputable def canonicalStableRawComponentSelfPairEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    (CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  let reference := canonicalStableRawComponentReferenceOwnerEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let natural := canonicalStableRawComponentSelfEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  let f : (CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component) →
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl self => reference self
    | Sum.inr self => natural self
  refine ⟨f, ?_⟩
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (reference.injective hxy)
      | inr y =>
          exact False.elim
            (canonicalStableRawComponentReferenceOwnerEmbedding_ne_self
              ends m j k l zero hloop hjk hkl hk0 p hno component x y hxy)
  | inr x =>
      cases y with
      | inl y =>
          exact False.elim
            (canonicalStableRawComponentReferenceOwnerEmbedding_ne_self
              ends m j k l zero hloop hjk hkl hk0 p hno component y x
                hxy.symm)
      | inr y => exact congrArg Sum.inr (natural.injective hxy)


end StatMech.GrahamGHS.FourColor
