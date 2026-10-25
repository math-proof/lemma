/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part15
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

noncomputable def canonicalStableRawComponentSuccessorToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component := by
  classical
  by_cases hself : s.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p s.1.source
  · exact ⟨canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself,
      (canonicalStableRawSelfOwnerReroute_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself).trans s.2⟩
  · exact ⟨canonicalStableRawDirectAlternateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself,
      (canonicalStableRawDirectAlternateLeftToken_fullComponent
        ends m j k l zero hloop hjk hkl hk0 p hno s.1 hself).trans s.2⟩


end StatMech.GrahamGHS.FourColor
