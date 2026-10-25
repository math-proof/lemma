/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc11core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc9core
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc7distinctwitnessclusters.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc11core
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths
open MeasureTheory


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc11_BoxOriginOpenIncidence (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∀ x₁ x₂ x₃ : Site d, x₁ ∈ box d n → x₂ ∈ box d n → x₃ ∈ box d n →
      (cluster d ω x₁).Infinite → (cluster d ω x₂).Infinite → (cluster d ω x₃).Infinite →
      cluster d ω x₁ ≠ cluster d ω x₂ → cluster d ω x₁ ≠ cluster d ω x₃ →
      cluster d ω x₂ ≠ cluster d ω x₃ →
      ∀ (a₁ a₂ a₃ : Site d) (W : Finset (Sym2 (Site d))),
        (∀ e ∈ W, (0 : Site d) ∉ e) →
        (hypercubicLattice d).Adj 0 a₁ → (hypercubicLattice d).Adj 0 a₂ →
        (hypercubicLattice d).Adj 0 a₃ →
        a₁ ∈ cluster d ω x₁ → a₂ ∈ cluster d ω x₂ → a₃ ∈ cluster d ω x₃ →
        (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁ ∧
          (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂ ∧
          (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃


end Walls
end StatMech
