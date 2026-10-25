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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part22


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareBondMateEquiv (n : Nat) (hn : 0 < n) :
    Equiv.Perm (FKIsingMedialDart (fkSquareBoxPlanar n)) where
  toFun := fkIsingSquareBondMate n hn
  invFun := fkIsingSquareBondMate n hn
  left_inv := fkIsingSquareBondMate_involutive n hn
  right_inv := fkIsingSquareBondMate_involutive n hn


def fkIsingSquareSourcePrimalEdge (n : Nat) (hn : 0 < n) :
    FKIsingMedialVertex (fkSquareBoxPlanar n) :=
  ⟨s(fkIsingSquareMarkedA n, fkIsingSquareAfterA n hn),
    (SimpleGraph.mem_edgeSet _).2 (fkIsingSquareMarkedA_adj_afterA n hn)⟩


def fkIsingSquareTerminalPrimalEdge (n : Nat) (hn : 0 < n) :
    FKIsingMedialVertex (fkSquareBoxPlanar n) :=
  ⟨s(fkIsingSquareMarkedB n, fkIsingSquareAfterB n hn),
    (SimpleGraph.mem_edgeSet _).2 (fkIsingSquareMarkedB_adj_afterB n hn)⟩


def fkIsingSquareSourceEdgeOrientation (n : Nat) (hn : 0 < n) :
    FKIsingSquareEdgeOrientation n (fkIsingSquareSourcePrimalEdge n hn) where
  tail := fkIsingSquareMarkedA n
  head := fkIsingSquareAfterA n hn
  edge_eq := rfl
  axis := .horizontal
  step := by
    funext i
    fin_cases i
    · simp [fkIsingSquareMarkedA, fkIsingSquareAfterA,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        Pi.add_apply]
      ring
    · simp [fkIsingSquareMarkedA, fkIsingSquareAfterA,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        Pi.add_apply]


def fkIsingSquareTerminalEdgeOrientation (n : Nat) (hn : 0 < n) :
    FKIsingSquareEdgeOrientation n (fkIsingSquareTerminalPrimalEdge n hn) where
  tail := fkIsingSquareAfterB n hn
  head := fkIsingSquareMarkedB n
  edge_eq := by
    change s(fkIsingSquareAfterB n hn, fkIsingSquareMarkedB n) =
      s(fkIsingSquareMarkedB n, fkIsingSquareAfterB n hn)
    rw [Sym2.eq_iff]
    exact Or.inr ⟨rfl, rfl⟩
  axis := .vertical
  step := by
    funext i
    fin_cases i <;>
      simp [fkIsingSquareMarkedB, fkIsingSquareAfterB,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        Pi.add_apply]

end
end StatMech.Universality
