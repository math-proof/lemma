/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualSubgraphSum.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity


namespace StatMech.FrontierA

open Finset Equiv

variable {D E : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]


structure RibbonPermutationSystem (E D : Type*)
    [Fintype D] [DecidableEq D] where
  rotation : Equiv.Perm D
  edgeFlip : E -> Equiv.Perm D
  edgeFlip_isSwap : forall e, (edgeFlip e).IsSwap
  edgeFlip_commute : forall e f, (e = f -> False) ->
    Commute (edgeFlip e) (edgeFlip f)

end StatMech.FrontierA
