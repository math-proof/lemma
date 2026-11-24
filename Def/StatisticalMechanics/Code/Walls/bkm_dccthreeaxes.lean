module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
open Set
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bkm_dccthreeaxes.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def corridorRay (j : Fin d) : Set (Site d) := {x | ∃ t : ℤ, x = hrHD_rayPt j t}


end StatMech.Walls
