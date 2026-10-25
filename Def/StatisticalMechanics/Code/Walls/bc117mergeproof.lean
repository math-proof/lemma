/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc115severance.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc34ray.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc117_BoxAdjacentExternalArm (d L n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∀ x₁ x₂ x₃ : Site d,
    x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
    (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
    cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
    cluster d ω x₂ ≠ cluster d ω x₃ →
    ∃ a₁ a₂ a₃ : Site d,
      (∃ b₁ ∈ bc61_boxAround d L 0, (openSubgraph d ω).Adj b₁ a₁) ∧
      (∃ b₂ ∈ bc61_boxAround d L 0, (openSubgraph d ω).Adj b₂ a₂) ∧
      (∃ b₃ ∈ bc61_boxAround d L 0, (openSubgraph d ω).Adj b₃ a₃) ∧
      (cluster d (removeSites (bc61_boxAround d L 0) ω) a₁).Infinite ∧
      (cluster d (removeSites (bc61_boxAround d L 0) ω) a₂).Infinite ∧
      (cluster d (removeSites (bc61_boxAround d L 0) ω) a₃).Infinite ∧
      cluster d ω x₁ = cluster d ω a₁ ∧ cluster d ω x₂ = cluster d ω a₂ ∧
      cluster d ω x₃ = cluster d ω a₃


end StatMech.Walls
