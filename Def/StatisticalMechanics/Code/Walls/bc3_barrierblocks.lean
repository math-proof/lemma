/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_barrierblocks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


def bc3_AdjClosed (ϱ : ConfigSpace (Sym2 (Site d))) (R : Set (Site d)) : Prop :=
  ∀ u v, u ∈ R → (openSubgraph d ϱ).Adj u v → v ∈ R


end Walls
end StatMech
