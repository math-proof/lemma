/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part11
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

theorem FiniteRelationCrossingContinuation.initialMatching_support
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    continuation.initialMatching.support =
      Finset.univ.erase (Sum.inl continuation.index) := by
  ext state
  cases state with
  | inl index =>
      by_cases hindex : index = continuation.index
      · subst index
        simp [StatMech.FrontierA.RelationPartialMatching.mem_support_iff,
          FiniteRelationCrossingContinuation.initialMatching]
      · simp [StatMech.FrontierA.RelationPartialMatching.mem_support_iff,
          FiniteRelationCrossingContinuation.initialMatching, hindex]
  | inr _ =>
      simp [StatMech.FrontierA.RelationPartialMatching.mem_support_iff,
        FiniteRelationCrossingContinuation.initialMatching]

theorem FiniteRelationCrossingContinuation.initialMatching_maximum
    {A : Type u} {B : Type v} {related : A -> B -> Prop}
    (continuation : FiniteRelationCrossingContinuation related) :
    continuation.initialMatching.IsMaximum := by
  intro other
  have hle := other.card_support_le_target
  have hle' : other.support.card ≤ continuation.size := by
    simpa only [FiniteRelationCrossingContinuation.Token,
      Fintype.card_fin] using hle
  rw [continuation.initialMatching_support]
  simp only [Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit]
  omega

end StatMech.GrahamGHS.FourColor
