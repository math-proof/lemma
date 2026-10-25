/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc8distinctcutclusters.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc8nocrossing.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc8cutleavesinfinite
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc8core
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths
open MeasureTheory


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc8_OriginRewiring (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)),
    (∀ e ∈ W, (0 : Site d) ∉ e) ∧
    ∃ a₁ a₂ a₃ : Site d,
      (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁ ∧
      (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂ ∧
      (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃ ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) a₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) a₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) a₃).Infinite ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) a₂ ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) a₃ ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) a₂ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) a₃


end Walls
end StatMech
