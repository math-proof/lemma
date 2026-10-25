/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part9
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

structure FiniteRelationCrossingContinuation
    {A : Type u} {B : Type v} (related : A -> B -> Prop) where
  size : Nat
  sources : Fin size ↪ A
  tokens : Fin size ↪ B
  extra : A
  index : Fin size
  extra_fresh : ∀ i, extra ≠ sources i
  aligned : ∀ i, related (sources i) (tokens i)
  crossing : related extra (tokens index)

end StatMech.GrahamGHS.FourColor
