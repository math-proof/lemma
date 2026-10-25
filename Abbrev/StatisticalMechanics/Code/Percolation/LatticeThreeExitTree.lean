/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ThreePendantTree
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d n : ℕ}


abbrev ThreeExitVertex (d n : ℕ) :=
  Sum (↑(boxFinsetBK d n) : Type) (Fin 3)


end StatMech.Percolation
