/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Instance.StatisticalMechanics.Code.Walls.bc20mengerroute
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


noncomputable def bc20_boxGraph (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d))) :
    SimpleGraph (box d m) :=
  (openSubgraph d ω).induce (box d m)


def bc20_originBox (d m : ℕ) : box d m := ⟨0, by intro i; simp⟩

end StatMech.Walls
