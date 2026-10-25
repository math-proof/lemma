/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc55route
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc56menger
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc56_BoxClusterReachesNbr (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      bc56_ClusterReachesNbr ω x₁ ∧ bc56_ClusterReachesNbr ω x₂ ∧ bc56_ClusterReachesNbr ω x₃


end StatMech.Walls
