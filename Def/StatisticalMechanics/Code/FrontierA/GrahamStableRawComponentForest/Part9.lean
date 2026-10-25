/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part8
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

def FiniteRelationDeficiencyOneFamily.extendPair
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (family : FiniteRelationDeficiencyOneFamily A B)
    (source : A) (token : B) (hsource : source ∉ family.states)
    (htoken : token ∉ family.tokens) : FiniteRelationDeficiencyOneFamily A B where
  states := insert source family.states
  tokens := insert token family.tokens
  deficiency_one := by
    rw [Finset.card_insert_of_notMem hsource,
      Finset.card_insert_of_notMem htoken]
    have hdeficiency := family.deficiency_one
    omega

end StatMech.GrahamGHS.FourColor
