/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part22
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

noncomputable def canonicalStableRawComponentSelfRank
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) : Nat :=
  canonicalStableRawSourceRank ends m j k l zero p self.1.source


noncomputable def canonicalStableRawComponentImmediateTerminals
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
  exact Finset.univ.filter fun terminal =>
    canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩ = Sum.inr terminal


noncomputable def canonicalStableRawComponentCollisionChildren
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
    Finset (CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  classical
  let Self := CanonicalStableRawComponentSelfState
    ends m j k l zero hloop hjk hkl hk0 p hno component
  letI : Fintype Self := Fintype.ofFinite Self
  let next := canonicalStableRawExceptionalEdgeNext
    ends m j k l zero hloop hjk hkl hk0 p hno self.1
  let stableBlock := canonicalStableRawStableCollisionTargetChildBlock
    ends m j k l zero hloop hjk hkl hk0 p hno component next.target
  let advancingBlock :=
    canonicalStableRawAdvancingCollisionSuccessorChildBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component next
  exact Finset.univ.filter fun child =>
    canonicalStableRawComponentSelfRank
        ends m j k l zero hloop hjk hkl hk0 p hno component child <
      canonicalStableRawComponentSelfRank
        ends m j k l zero hloop hjk hkl hk0 p hno component self ∧
    ((∃ collision ∈ stableBlock, collision.1.1 = child) ∨
      ∃ collision ∈ advancingBlock, collision.1.1 = child)

end StatMech.GrahamGHS.FourColor
