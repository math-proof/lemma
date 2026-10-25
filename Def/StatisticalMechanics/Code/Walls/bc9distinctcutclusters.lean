/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9distinctcutclusters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc8core.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc8distinctcutclusters.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc8nocrossing.Part2
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc9_DistinctCutClusters (d n : ℕ) : Prop :=
  (∀ ω ∈ threeMeetBox d n,
      ∃ x₁ x₂ x₃ : Site d,
        (cluster d (removeSite 0 ω) x₁).Infinite ∧
        (cluster d (removeSite 0 ω) x₂).Infinite ∧
        (cluster d (removeSite 0 ω) x₃).Infinite ∧
        cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
        cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
        cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d),
      cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y →
        ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x →
          ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y →
            ¬ IsOpenEdge d (removeSite 0 ω) u v)


end Walls
end StatMech
