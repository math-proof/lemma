module
public import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
public import Theorem.StatisticalMechanics.Code.Percolation.ThreePendantTree
public import Def.StatisticalMechanics.Code.Percolation.LatticeThreeExitTree
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Percolation

variable {d n : ℕ}


instance (inside : Fin 3 → Site d) : DecidableRel (threeExitGraph (n := n) inside).Adj :=
  fun a b => by cases a <;> cases b <;> simp [threeExitGraph] <;> infer_instance


end StatMech.Percolation
