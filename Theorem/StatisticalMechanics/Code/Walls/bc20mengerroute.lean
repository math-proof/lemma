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
import Def.StatisticalMechanics.Code.Walls.bc20mengerroute
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


@[simp] theorem bc20_originBox_coe (d m : ℕ) : (bc20_originBox d m : Site d) = 0 := rfl


theorem bc20_hardDir_boxGraph (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (A B : Set (box d m)) : bc17_HardDir (bc20_boxGraph d m ω) A B :=
  bc19_hardDir_all (bc20_boxGraph d m ω) A B


end StatMech.Walls
