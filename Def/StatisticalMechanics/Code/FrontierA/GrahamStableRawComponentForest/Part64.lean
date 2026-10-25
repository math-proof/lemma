/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part13
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

def CanonicalStableRawComponentBalancedDirectBlock.postSecondInitialState
    {ends : I → Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) : block.PostSecondContinuationState :=
  ⟨(Sum.inl (), Sum.inr entrance), by simp⟩

noncomputable def
    CanonicalStableRawComponentBalancedDirectBlock.postSecondContinuationStep
    {ends : I → Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (entrance : Fin block.size) :
    block.PostSecondContinuationState →
      block.PostSecondContinuationState ⊕
        (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component ⊕ Unit) :=
  partialForestNonbacktrackingStep (block.postSecondStep entrance)
    (block.postSecondStep_continuation_ne entrance)


end StatMech.GrahamGHS.FourColor
