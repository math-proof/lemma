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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part21


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareOrientedEdge_source (n : Nat) (hn : 0 < n) :
    fkIsingSquareOrientedEdge n (fkIsingSquareSourcePrimalEdge n hn) =
      fkIsingSquareSourceEdgeOrientation n hn :=
  fkIsingSquareOrientedEdge_unique n _ _ _

theorem fkIsingSquareOrientedEdge_terminal (n : Nat) (hn : 0 < n) :
    fkIsingSquareOrientedEdge n (fkIsingSquareTerminalPrimalEdge n hn) =
      fkIsingSquareTerminalEdgeOrientation n hn :=
  fkIsingSquareOrientedEdge_unique n _ _ _

theorem fkIsingSquareMarkedA_ne_markedB (n : Nat) (hn : 0 < n) :
    fkIsingSquareMarkedA n ≠ fkIsingSquareMarkedB n := by
  intro h
  have h1 := congrArg (fun x : (fkSquareBoxPlanar n).V => x.1 1) h
  simp [fkIsingSquareMarkedA, fkIsingSquareMarkedB] at h1
  omega

theorem fkIsingSquareMarkedA_not_adj_markedB (n : Nat) (hn : 0 < n) :
    ¬(fkSquareBoxPlanar n).G.Adj
      (fkIsingSquareMarkedA n) (fkIsingSquareMarkedB n) := by
  change ¬(hypercubicLattice 2).Adj
    (![-(n : Int), -(n : Int)] : Site 2)
    (![-(n : Int), (n : Int)] : Site 2)
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp
  omega

theorem adj_of_mem_edge_of_ne {V : Type*} (G : SimpleGraph V)
    (e : G.edgeSet) {x y : V} (hx : x ∈ e.1) (hy : y ∈ e.1)
    (hxy : x ≠ y) : G.Adj x y := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      rw [Sym2.mem_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact False.elim (hxy rfl)
      · exact he
      · exact he.symm
      · exact False.elim (hxy rfl)


end
end StatMech.Universality
