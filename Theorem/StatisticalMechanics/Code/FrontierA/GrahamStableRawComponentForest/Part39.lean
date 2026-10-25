/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part39
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

theorem canonicalStableRawComponentReferenceTerminal_mem_of_step_inr
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentReferenceStepEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component self =
      Sum.inr terminal) :
    terminal ∈ canonicalStableRawComponentReferenceTerminalClosure
      ends m j k l zero hloop hjk hkl hk0 p hno component self := by
  classical
  unfold canonicalStableRawComponentReferenceTerminalClosure
  apply FiniteRankTerminalSystem.terminals_subset_terminalClosure
    (canonicalStableRawComponentReferenceTerminalSystem
      ends m j k l zero hloop hjk hkl hk0 p hno component) self
  unfold canonicalStableRawComponentReferenceTerminalSystem
    canonicalStableRawComponentReferenceImmediateTerminals
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstep⟩

theorem canonicalStableRawComponentReferenceChild_terminalClosure_subset
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self child : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hchild : child ∈ canonicalStableRawComponentReferenceChildren
      ends m j k l zero hloop hjk hkl hk0 p hno component self) :
    canonicalStableRawComponentReferenceTerminalClosure
        ends m j k l zero hloop hjk hkl hk0 p hno component child ⊆
      canonicalStableRawComponentReferenceTerminalClosure
        ends m j k l zero hloop hjk hkl hk0 p hno component self := by
  classical
  unfold canonicalStableRawComponentReferenceTerminalClosure
  exact FiniteRankTerminalSystem.terminalClosure_subset_of_mem_children
    (canonicalStableRawComponentReferenceTerminalSystem
      ends m j k l zero hloop hjk hkl hk0 p hno component) hchild


theorem canonicalStableRawTokenComponent_embedding_of_forestStepInjective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (hinjective : Function.Injective
      (canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Nonempty (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  let forest : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component ↪
      (CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component ⊕
        CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component) :=
    ⟨canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component, hinjective⟩
  exact ⟨forest.trans
    (canonicalStableRawComponentDirectSumNonexceptionalEquivToken
      ends m j k l zero hloop hjk hkl hk0 p hno component).toEmbedding⟩


end StatMech.GrahamGHS.FourColor
