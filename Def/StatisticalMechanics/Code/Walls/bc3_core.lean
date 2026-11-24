module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
public import Theorem.StatisticalMechanics.Code.Walls.bc3_barrierblocks
public import Theorem.StatisticalMechanics.Code.Walls.bc3_rhoedgecases
public import Theorem.StatisticalMechanics.Code.Walls.bc3_anchordecomp.Part2
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

variable {d : ℕ}


def bc3_clusterNbhd (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) : Set (Site d) :=
  ⋃ (t : ℕ) (_ : 1 ≤ t ∧ t ≤ L), cluster d (removeSite 0 ω) (hrHD_rayPt j (t : ℤ))


end Walls
end StatMech
