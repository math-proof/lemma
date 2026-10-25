/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part24
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

noncomputable def canonicalStableRawComponentDirectSumNonexceptionalEquivToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    (CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
      CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) ≃
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let exceptional := fun token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component =>
    CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p token.1
  exact (Equiv.sumCongr
    (canonicalStableRawComponentDirectStateEquivExceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (Equiv.refl _)).trans (Equiv.sumCompl exceptional)


noncomputable def canonicalStableRawComponentReferenceOwnerEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let f := fun self : CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component =>
    canonicalStableRawComponentAlternateToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩
  refine ⟨f, ?_⟩
  intro self other htoken
  apply Subtype.ext
  apply canonicalStableRawReferenceOwnerLeftToken_eq_imp
    ends m j k l zero hloop hjk hkl hk0 p
      self.1 other.1 self.2.2 other.2.2
  have hraw := congrArg Subtype.val htoken
  unfold f canonicalStableRawComponentAlternateToken at hraw
  rw [dif_pos self.2.2, dif_pos other.2.2] at hraw
  exact hraw


end StatMech.GrahamGHS.FourColor
