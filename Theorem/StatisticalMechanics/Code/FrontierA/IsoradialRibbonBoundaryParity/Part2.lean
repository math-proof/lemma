/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualSubgraphSum.Part3
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity


namespace StatMech.FrontierA

open Finset Equiv

variable {D E : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]


namespace RibbonPermutationSystem

variable (R : RibbonPermutationSystem E D)

omit [Fintype E] [DecidableEq E] in
theorem edgeFlip_pairwise (F : Finset E) :
    (F : Set E).Pairwise fun e f => Commute (R.edgeFlip e) (R.edgeFlip f) := by
  intro e _ f _ hef
  exact R.edgeFlip_commute e f hef


end RibbonPermutationSystem
end StatMech.FrontierA
