/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactVariation.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareRadialPatchCellPrimalTail
    (m : Nat) (c : FKIsingSquareRadialPatchInteriorCell m) :
    FKIsingSquareRadialPatchPrimalNode m := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · exact ⟨(⟨c.1.1, by omega⟩, ⟨c.2.1, by omega⟩), h⟩
  · exact ⟨(⟨c.1.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.1⟩,
      ⟨c.2.1, by omega⟩), by
      change Even ((c.1.1 + 1) + c.2.1)
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega⟩

noncomputable def fkIsingSquareRadialPatchCellPrimalHead
    (m : Nat) (c : FKIsingSquareRadialPatchInteriorCell m) :
    FKIsingSquareRadialPatchPrimalNode m := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · exact ⟨(⟨c.1.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.1⟩,
      ⟨c.2.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.2⟩), by
      change Even ((c.1.1 + 1) + (c.2.1 + 1))
      rw [Nat.even_iff]
      have hmod := Nat.even_iff.mp h
      omega⟩
  · exact ⟨(⟨c.1.1, by omega⟩,
      ⟨c.2.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.2⟩), by
      change Even (c.1.1 + (c.2.1 + 1))
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega⟩

noncomputable def fkIsingSquareRadialPatchCellDualTail
    (m : Nat) (c : FKIsingSquareRadialPatchInteriorCell m) :
    FKIsingSquareRadialPatchDualNode m := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · exact ⟨(⟨c.1.1, by omega⟩,
      ⟨c.2.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.2⟩), by
      change ¬ Even (c.1.1 + (c.2.1 + 1))
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp h
      omega⟩
  · exact ⟨(⟨c.1.1, by omega⟩, ⟨c.2.1, by omega⟩), h⟩

noncomputable def fkIsingSquareRadialPatchCellDualHead
    (m : Nat) (c : FKIsingSquareRadialPatchInteriorCell m) :
    FKIsingSquareRadialPatchDualNode m := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · exact ⟨(⟨c.1.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.1⟩,
      ⟨c.2.1, by omega⟩), by
      change ¬ Even ((c.1.1 + 1) + c.2.1)
      rw [Nat.not_even_iff]
      have hmod := Nat.even_iff.mp h
      omega⟩
  · exact ⟨(⟨c.1.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.1⟩,
      ⟨c.2.1 + 1, by
        exact fkIsingSquareRadialPatchInteriorCell_succ_lt c.2⟩), by
      change ¬ Even ((c.1.1 + 1) + (c.2.1 + 1))
      rw [Nat.not_even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega⟩

noncomputable def fkIsingSquareRadialPatchCellPrimalDart
    (n m : Nat) (hm : m ≤ n) (c : FKIsingSquareRadialPatchInteriorCell m) :
    (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart := by
  classical
  refine ⟨(fkIsingSquareRadialPatchCellPrimalTail m c,
    fkIsingSquareRadialPatchCellPrimalHead m c), ?_⟩
  change (fkSquareBoxPlanar n).G.Adj
    (fkIsingSquareRadialPatchPrimalNodeVertex n m hm
      (fkIsingSquareRadialPatchCellPrimalTail m c))
    (fkIsingSquareRadialPatchPrimalNodeVertex n m hm
      (fkIsingSquareRadialPatchCellPrimalHead m c))
  by_cases h : Even (c.1.1 + c.2.1)
  · simp only [fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead, h, dif_pos]
    change (fkSquareBoxPlanar n).G.Adj
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨c.1.1 + 1, by omega⟩ ⟨c.2.1 + 1, by omega⟩)
    rw [fkIsingSquareRadialPatchVertex_northeast_eq_neighbor_east
      n m c.1.1 c.2.1 hm
      (fkIsingSquareRadialPatchInteriorCell_succ_lt c.1)
      (fkIsingSquareRadialPatchInteriorCell_succ_lt c.2) h]
    exact fkIsingSquare_adj_neighbor n _ .east _
  · have heven : Even ((c.1.1 + 1) + c.2.1) := by
      rw [Nat.even_iff]
      have hmod := Nat.not_even_iff.mp h
      omega
    simp only [fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead, h]
    change (fkSquareBoxPlanar n).G.Adj
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨c.1.1 + 1, by omega⟩ ⟨c.2.1, by omega⟩)
      (fkIsingSquareRadialPatchVertex n m hm
        ⟨c.1.1, by omega⟩ ⟨c.2.1 + 1, by omega⟩)
    have hse := fkIsingSquareRadialPatchVertex_southeast_eq_neighbor_south
      n m (c.1.1 + 1) c.2.1 hm (by omega)
      (fkIsingSquareRadialPatchInteriorCell_succ_lt c.2)
      (fkIsingSquareRadialPatchInteriorCell_succ_lt c.1) heven
    simp only [Nat.add_sub_cancel] at hse
    rw [hse]
    exact fkIsingSquare_adj_neighbor n _ .south _

noncomputable def fkIsingSquareRadialPatchCellDualDart
    (m : Nat) (c : FKIsingSquareRadialPatchInteriorCell m) :
    (fkIsingSquareRadialPatchDualGraph m).Dart := by
  classical
  refine ⟨(fkIsingSquareRadialPatchCellDualTail m c,
    fkIsingSquareRadialPatchCellDualHead m c), ?_⟩
  change
    ((_ + 1 = _) ∨ (_ + 1 = _)) ∧ ((_ + 1 = _) ∨ (_ + 1 = _))
  by_cases h : Even (c.1.1 + c.2.1) <;>
    simp [fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead, h]

end
end StatMech.Universality
