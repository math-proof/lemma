/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualSubgraphSum.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity.Part2


namespace StatMech.FrontierA

open Finset Equiv

variable {D E : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]


namespace RibbonPermutationSystem

variable (R : RibbonPermutationSystem E D)

noncomputable def partialEdgeFlip (F : Finset E) : Equiv.Perm D :=
  F.noncommProd R.edgeFlip (R.edgeFlip_pairwise F)


noncomputable def boundaryPerm (F : Finset E) : Equiv.Perm D :=
  R.rotation * R.partialEdgeFlip F


noncomputable def boundaryComponents (F : Finset E) : Nat :=
  permCycleCount (R.boundaryPerm F)

end RibbonPermutationSystem
end StatMech.FrontierA
