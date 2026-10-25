/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualSubgraphSum.Part3


namespace StatMech.FrontierA

open Finset Equiv

variable {D E : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]


def permCycleCount (sigma : Equiv.Perm D) : Nat :=
  Multiset.card sigma.cycleType +
    (Fintype.card D - sigma.cycleType.sum)

end StatMech.FrontierA
