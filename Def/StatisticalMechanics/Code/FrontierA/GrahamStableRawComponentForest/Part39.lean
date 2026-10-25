/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part38
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

noncomputable def canonicalStableRawComponentReferenceTerminalSystem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)) :
    FiniteRankTerminalSystem
      (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) where
  rank := canonicalStableRawComponentSelfRank
    ends m j k l zero hloop hjk hkl hk0 p hno component
  terminals := canonicalStableRawComponentReferenceImmediateTerminals
    ends m j k l zero hloop hjk hkl hk0 p hno component
  children := canonicalStableRawComponentReferenceChildren
    ends m j k l zero hloop hjk hkl hk0 p hno component
  children_rank_lt := canonicalStableRawComponentReferenceChildren_rank_lt
    ends m j k l zero hloop hjk hkl hk0 p hno component


noncomputable def canonicalStableRawComponentReferenceTerminalNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Finset (CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  exact sources.biUnion
    (canonicalStableRawComponentReferenceTerminalSystem
      ends m j k l zero hloop hjk hkl hk0 p hno component
        |>.terminalClosure)


noncomputable def canonicalStableRawComponentReferenceTerminalClosure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Finset (CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  exact (canonicalStableRawComponentReferenceTerminalSystem
    ends m j k l zero hloop hjk hkl hk0 p hno component).terminalClosure self

end StatMech.GrahamGHS.FourColor
