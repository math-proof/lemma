/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc6core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc7offboxedgeagree
import Theorem.StatisticalMechanics.Code.Walls.bc7crossaxisunique
import Theorem.StatisticalMechanics.Code.Walls.bc7rayPtoffboxneighbor
import Theorem.StatisticalMechanics.Code.Walls.bc7nocrossing
import Theorem.StatisticalMechanics.Code.Walls.bc7offboxsubsetcluster
import Theorem.StatisticalMechanics.Code.Walls.bc7offboxclusterbasics.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc7distinctwitnessclusters.Part2
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc6_ReentryOnRay (N : ℕ) (a : Fin d) (G : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∀ u v : Site d, u ∈ bc6_offBoxCluster N a (N + 1) ω →
    IsOpenEdge d (removeSite 0 ω) u v →
    s(u, v) ∉ G → s(u, v) ∉ boxEdges d N → v ∈ box d N →
    v ∈ bc6_rayInterior a (N + 1)


end Walls
end StatMech
