/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc3_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc3_barrierblocks
import Theorem.StatisticalMechanics.Code.Walls.bc3_anchordecomp.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc6edgedichotomy
import Theorem.StatisticalMechanics.Code.Walls.bc6corridoraxisunique
import Theorem.StatisticalMechanics.Code.Walls.bc6raysetdef.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc6stepsameray
import Theorem.StatisticalMechanics.Code.Walls.bc6core
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc6_ArmClosed (N : ℕ) (a : Fin d) (R : ℕ) (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∀ u v : Site d, u ∈ bc6_offBoxCluster N a R ω →
    IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v →
    v ∈ bc6_offBoxCluster N a R ω ∨ v ∈ bc6_rayInterior a R


end Walls
end StatMech
