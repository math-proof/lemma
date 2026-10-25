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
import Theorem.StatisticalMechanics.Code.Walls.bc20mengerroute.Part3
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


universe u

variable {V : Type u} [DecidableEq V] {GG : SimpleGraph V}

def bc20_boundaryV (d m : ℕ) : Set (box d m) := {v | (v : Site d) ∈ vertexBoundary d m}


def bc20_shellV (d m R : ℕ) : Set (box d m) := {v | (v : Site d) ∈ vertexBoundary d R}


end StatMech.Walls
