/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc3_barrierblocks
import Theorem.StatisticalMechanics.Code.Walls.bc3_rhoedgecases
import Theorem.StatisticalMechanics.Code.Walls.bc3_anchordecomp.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc3_core
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc3_CrossDisjoint (ω : ConfigSpace (Sym2 (Site d)))
    (a c : Fin d) (R L : ℕ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → p ≤ L → hrHD_rayPt c (p : ℤ) ∉ bc3_clusterNbhd ω a R


end Walls
end StatMech
