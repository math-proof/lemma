/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_raydisjoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccthreeaxes
import Theorem.StatisticalMechanics.Code.Walls.bc2_raydisjoint
open Set
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc2_corridorVerts (j : Fin d) (L : ℕ) : Set (Site d) :=
  {x | ∃ e ∈ hrHD_corridorEdges j L, x ∈ e}


end StatMech.Walls
