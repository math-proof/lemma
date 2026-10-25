/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxclusterbasics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc6raysetdef.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc7offboxclusterbasics
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc7_offBoxClusterBasics (N : ℕ) (a : Fin d) (R : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  (hrHD_rayPt a (R : ℤ)) ∈ bc6_offBoxCluster N a R ω ∧
    bc6_offBoxCluster N a R ω ⊆ (box d N)ᶜ


end Walls
end StatMech
