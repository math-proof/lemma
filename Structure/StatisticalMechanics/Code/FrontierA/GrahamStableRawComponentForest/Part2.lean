/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part2
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


structure FiniteRelationMinimalTightProblem where
  State : Type u
  Token : Type v
  [stateFintype : Fintype State]
  [stateDecidableEq : DecidableEq State]
  [tokenFintype : Fintype Token]
  [tokenDecidableEq : DecidableEq Token]
  incident : State -> Token -> Prop
  carrier : Finset State
  nonempty : carrier.Nonempty
  deficiency_one :
    (finiteBipartiteRelationNeighborhood incident carrier).card + 1 =
      carrier.card
  erase_invariant : ∀ source ∈ carrier,
    finiteBipartiteRelationNeighborhood incident (carrier.erase source) =
      finiteBipartiteRelationNeighborhood incident carrier
  proper_hall : ∀ smaller : Finset State, smaller ⊂ carrier ->
    smaller.card ≤
      (finiteBipartiteRelationNeighborhood incident smaller).card

end StatMech.GrahamGHS.FourColor
