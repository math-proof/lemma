/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8nocrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc7nocrossing
import Theorem.StatisticalMechanics.Code.Walls.bc8distinctcutclusters.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc8nocrossing
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc8_NoCrossing (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) : Prop :=
  (cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y ↔
      ¬ Connected d (removeSite 0 ω) x y) ∧
    (Disjoint (cluster d (removeSite 0 ω) x) (cluster d (removeSite 0 ω) y) ↔
      ¬ Connected d (removeSite 0 ω) x y) ∧
    (cluster d (removeSite 0 ω) x ≠ cluster d (removeSite 0 ω) y →
      ∀ ⦃u : Site d⦄, u ∈ cluster d (removeSite 0 ω) x →
        ∀ ⦃v : Site d⦄, v ∈ cluster d (removeSite 0 ω) y →
          ¬ IsOpenEdge d (removeSite 0 ω) u v)


end Walls
end StatMech
