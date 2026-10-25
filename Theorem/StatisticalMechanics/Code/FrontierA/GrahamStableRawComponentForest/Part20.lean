/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part20
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

theorem canonicalStableRawComponentForestStep_direct_split
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨direct.1, direct.2.1⟩ = Sum.inr terminal) ∨
      ∃ continuation : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component
              ⟨direct.1, direct.2.1⟩ = Sum.inl continuation ∧
          let next := canonicalStableRawExceptionalEdgeNext
            ends m j k l zero hloop hjk hkl hk0 p hno direct.1
          continuation.1 = next ∨
            (continuation.1.source ≠ next.source ∧
              continuation.1.target = next.target) := by
  classical
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨direct.1, direct.2.1⟩).1
  · right
    let continuation := canonicalStableRawComponentExceptionalSuccessorDirect
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨direct.1, direct.2.1⟩ hexceptional
    refine ⟨continuation, ?_, ?_⟩
    · unfold canonicalStableRawComponentForestStep
      rw [dif_pos hexceptional]
    · exact
        canonicalStableRawComponentExceptionalSuccessorDirect_next_or_sibling_of_direct
          ends m j k l zero hloop hjk hkl hk0 p hno component
            direct hexceptional
  · left
    let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨direct.1, direct.2.1⟩, hexceptional⟩
    refine ⟨terminal, ?_⟩
    unfold canonicalStableRawComponentForestStep
    rw [dif_neg hexceptional]


theorem canonicalStableRawComponentForestStep_direct_next_or_sibling_of_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (direct continuation : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨direct.1, direct.2.1⟩ = Sum.inl continuation) :
    let next := canonicalStableRawExceptionalEdgeNext
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1
    continuation.1 = next ∨
      (continuation.1.source ≠ next.source ∧
        continuation.1.target = next.target) := by
  dsimp only
  rcases canonicalStableRawComponentForestStep_direct_split
      ends m j k l zero hloop hjk hkl hk0 p hno component direct with
    ⟨terminal, hterminal⟩ | ⟨nextDirect, hnextDirect, hkind⟩
  · rw [hstep] at hterminal
    contradiction
  · have heq : nextDirect = continuation := Sum.inl.inj
      (hnextDirect.symm.trans hstep)
    simpa only [heq] using hkind


end StatMech.GrahamGHS.FourColor
