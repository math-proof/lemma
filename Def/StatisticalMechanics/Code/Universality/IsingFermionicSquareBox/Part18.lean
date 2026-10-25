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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part19


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareDirectionEdgeOrientation (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    FKIsingSquareEdgeOrientation n
      (fkIsingSquareDirectionEdge n u d hd) := by
  cases d
  · exact ⟨u, fkIsingSquareNeighbor n u .east hd,
      rfl, .horizontal, rfl⟩
  · exact ⟨u, fkIsingSquareNeighbor n u .north hd,
      rfl, .vertical, rfl⟩
  · refine ⟨fkIsingSquareNeighbor n u .west hd, u,
      ?_, .horizontal, ?_⟩
    · change s(fkIsingSquareNeighbor n u .west hd, u) =
        s(u, fkIsingSquareNeighbor n u .west hd)
      rw [Sym2.eq_iff]
      exact Or.inr ⟨rfl, rfl⟩
    · simp only
      funext i
      fin_cases i <;>
        simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          Pi.add_apply] <;> rfl
  · refine ⟨fkIsingSquareNeighbor n u .south hd, u,
      ?_, .vertical, ?_⟩
    · change s(fkIsingSquareNeighbor n u .south hd, u) =
        s(u, fkIsingSquareNeighbor n u .south hd)
      rw [Sym2.eq_iff]
      exact Or.inr ⟨rfl, rfl⟩
    · simp only
      funext i
      fin_cases i <;>
        simp [fkIsingSquareNeighbor, fkIsingSquareNeighborSite,
          Pi.add_apply] <;> rfl


end
end StatMech.Universality
