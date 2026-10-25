/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc8core.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc9nbrcutcluster
import Theorem.StatisticalMechanics.Code.Walls.bc9cutsurvives
import Theorem.StatisticalMechanics.Code.Walls.bc9distinctcutclusters
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths
open MeasureTheory


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc9_BoxOriginReach (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)),
    (∀ e ∈ W, (0 : Site d) ∉ e) ∧
    ∃ y₁ y₂ y₃ : Site d,
      y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧
      Connected d (forceOpenFinset W ω) 0 y₁ ∧
      Connected d (forceOpenFinset W ω) 0 y₂ ∧
      Connected d (forceOpenFinset W ω) 0 y₃ ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) y₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) y₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset W ω)) y₃).Infinite ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ ∧
      cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ≠
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₃


end Walls
end StatMech
