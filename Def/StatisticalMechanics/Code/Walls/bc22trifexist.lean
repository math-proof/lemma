module
public import Theorem.StatisticalMechanics.Code.Walls.bc20mengerroute.Part5
public import Theorem.StatisticalMechanics.Code.Walls.bc21trifurc.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part4
public import Theorem.StatisticalMechanics.Code.Walls.bc22trifexist
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

variable {d : ℕ}


universe u

variable {V : Type u} {GG : SimpleGraph V}


def bc22_BoxThreeBranchMinCut (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n, bka_MergeFree ω


end StatMech.Walls
