/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.FiniteComplementConnected
import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ArcNoSeparation.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ArcExteriorClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.LeafRemovableClose
open Set SimpleGraph


namespace StatMech

namespace Lattice

def lrc_ringS : Set (Site 2) :=
  {![1, 1], ![1, -1], ![0, 1], ![0, -1], ![-1, 1], ![-1, 0], ![-1, -1]}


def lrc_uPrime : Site 2 := ![1, 0]


end Lattice
end StatMech
