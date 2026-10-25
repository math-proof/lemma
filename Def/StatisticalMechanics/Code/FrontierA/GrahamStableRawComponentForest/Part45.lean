/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part9
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

noncomputable def canonicalStableRawComponentTightForestStep
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : ↑sources) :
    CanonicalStableRawComponentTightDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component sources ⊕
      CanonicalStableRawComponentTightTerminalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  cases hstep : canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 with
  | inl direct =>
      refine Sum.inl ⟨direct, ?_⟩
      have htoken := canonicalStableRawComponentForestStep_token
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1
      rw [hstep] at htoken
      change canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct =
        canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1 at htoken
      rw [htoken]
      exact (canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources state).2
  | inr terminal =>
      refine Sum.inr ⟨terminal, ?_⟩
      have htoken := canonicalStableRawComponentForestStep_token
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1
      rw [hstep] at htoken
      change terminal.1 = canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1 at htoken
      rw [htoken]
      exact (canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources state).2


end StatMech.GrahamGHS.FourColor
