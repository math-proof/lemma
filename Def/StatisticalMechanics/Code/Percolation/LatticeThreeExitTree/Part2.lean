/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ThreePendantTree
import Instance.StatisticalMechanics.Code.Percolation.LatticeThreeExitTree
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d n : ℕ}


def threeExitTip (i : Fin 3) : ThreeExitVertex d n := Sum.inr i

end StatMech.Percolation
