/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeThreeExitTree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ThreePendantTree
import Abbrev.StatisticalMechanics.Code.Percolation.LatticeThreeExitTree
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d n : ℕ}


def threeExitGraph (inside : Fin 3 → Site d) :
    SimpleGraph (ThreeExitVertex d n) where
  Adj a b := match a, b with
    | Sum.inl x, Sum.inl y => (hypercubicLattice d).Adj x.1 y.1
    | Sum.inl x, Sum.inr i => x.1 = inside i
    | Sum.inr i, Sum.inl x => x.1 = inside i
    | Sum.inr _, Sum.inr _ => False
  symm := by
    constructor
    intro a b
    cases a <;> cases b <;> simp_all [adj_comm]
  loopless := ⟨by
    rintro (x | i)
    · exact (hypercubicLattice d).irrefl
    · simp⟩

end StatMech.Percolation
