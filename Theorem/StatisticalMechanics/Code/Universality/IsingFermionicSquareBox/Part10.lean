/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part9


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareMarkedA_adj_afterA (n : Nat) (hn : 0 < n) :
    (fkSquareBoxPlanar n).G.Adj
      (fkIsingSquareMarkedA n) (fkIsingSquareAfterA n hn) := by
  change (hypercubicLattice 2).Adj
    (![-(n : Int), -(n : Int)] : Site 2)
    (![(1 : Int) - n, -(n : Int)] : Site 2)
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp [show -(n : Int) - ((1 : Int) - n) = -1 by ring]

theorem fkIsingSquareMarkedB_adj_afterB (n : Nat) (hn : 0 < n) :
    (fkSquareBoxPlanar n).G.Adj
      (fkIsingSquareMarkedB n) (fkIsingSquareAfterB n hn) := by
  change (hypercubicLattice 2).Adj
    (![-(n : Int), (n : Int)] : Site 2)
    (![-(n : Int), (n : Int) - 1] : Site 2)
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp


end
end StatMech.Universality
