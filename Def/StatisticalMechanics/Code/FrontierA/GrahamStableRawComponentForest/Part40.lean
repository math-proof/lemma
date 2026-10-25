/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part39
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

noncomputable def canonicalStableRawComponentStateEquivSelfSumDirect
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ≃
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  let split : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component →
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component := fun s =>
    if hself : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source then
      Sum.inl ⟨s.1, s.2, hself⟩
    else
      Sum.inr ⟨s.1, s.2, hself⟩
  let recover :
      CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component →
      CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component
    | Sum.inl s => ⟨s.1, s.2.1⟩
    | Sum.inr s => ⟨s.1, s.2.1⟩
  refine ⟨split, recover, ?_, ?_⟩
  · intro s
    by_cases hself : s.1.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p s.1.source
    · simp [split, recover, hself]
    · simp [split, recover, hself]
  · intro s
    cases s with
    | inl s => simp [split, recover, s.2.2]
    | inr s => simp [split, recover, s.2.2]


end StatMech.GrahamGHS.FourColor
