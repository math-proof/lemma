/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part12
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

def FiniteRelationDeficiencyOneFamily.threeTwo
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x y : B) (hxy : x ≠ y) : FiniteRelationDeficiencyOneFamily A B where
  states := {a, b, c}
  tokens := {x, y}
  deficiency_one := by
    simp [hab, hac, hbc, hxy]


end StatMech.GrahamGHS.FourColor
