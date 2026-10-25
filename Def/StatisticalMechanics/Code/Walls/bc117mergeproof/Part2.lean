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
import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part2
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


def bc117_ClustersMeetOriginBox (L n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox 2 n, ∀ x₁ x₂ x₃ : Site 2,
    x₁ ∈ box 2 n → x₂ ∈ box 2 n → x₃ ∈ box 2 n →
    (cluster 2 ω x₁).Infinite → (cluster 2 ω x₂).Infinite → (cluster 2 ω x₃).Infinite →
    cluster 2 ω x₁ ≠ cluster 2 ω x₂ → cluster 2 ω x₁ ≠ cluster 2 ω x₃ →
    cluster 2 ω x₂ ≠ cluster 2 ω x₃ →
    ∃ x₁' x₂' x₃' : Site 2,
      x₁' ∈ bc61_boxAround 2 L 0 ∧ x₂' ∈ bc61_boxAround 2 L 0 ∧ x₃' ∈ bc61_boxAround 2 L 0 ∧
      cluster 2 ω x₁ = cluster 2 ω x₁' ∧ cluster 2 ω x₂ = cluster 2 ω x₂' ∧
      cluster 2 ω x₃ = cluster 2 ω x₃'


end StatMech.Walls
