module
public import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
public import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

variable {d : ℕ}


noncomputable instance bc20_boxFintype (d m : ℕ) : Fintype (box d m) :=
  (box_finite d m).fintype


end StatMech.Walls
