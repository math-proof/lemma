/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bscsupercut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfinfinalclose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

#check @bfin_SuperCutBridge


def bsc_IsBoxCentre (L : ℕ) (y : Site d) : Prop :=
  ∀ x : Site d, x ∈ bc61_boxAround d L y ↔ bgn_idx L x = bgn_idx L y


end StatMech.Walls
