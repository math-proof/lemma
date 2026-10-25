/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc85bootstrap
import Theorem.StatisticalMechanics.Code.Walls.bc81gncutae
import Theorem.StatisticalMechanics.Code.Walls.bc83genuinetrif.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc76buffer.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc93_BadBox (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y' : Site d) : Prop :=
  ∃ a b : Site d, a ∈ bc61_boxAround d L y' ∧ b ∈ bc61_boxAround d L y' ∧
    (cluster d ω a).Infinite ∧ (cluster d ω b).Infinite ∧ ¬ Connected d ω a b


end StatMech.Walls
