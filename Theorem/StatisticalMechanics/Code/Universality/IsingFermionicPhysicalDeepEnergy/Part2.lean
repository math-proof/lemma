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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchCellPrimalDart_injective
    (n m : Nat) (hm : m ≤ n) :
    Function.Injective (fkIsingSquareRadialPatchCellPrimalDart n m hm) := by
  classical
  intro c d hcd
  have hcoords := congrArg (fun e :
      (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart ↦
        (e.fst.1.1.1, e.fst.1.2.1, e.snd.1.1.1, e.snd.1.2.1)) hcd
  by_cases hc : Even (c.1.1 + c.2.1) <;>
    by_cases hd : Even (d.1.1 + d.2.1) <;>
    simp [fkIsingSquareRadialPatchCellPrimalDart,
      fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead, hc, hd] at hcoords <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

theorem fkIsingSquareRadialPatchCellDualDart_injective (m : Nat) :
    Function.Injective (fkIsingSquareRadialPatchCellDualDart m) := by
  classical
  intro c d hcd
  have hcoords := congrArg (fun e :
      (fkIsingSquareRadialPatchDualGraph m).Dart ↦
        (e.fst.1.1.1, e.fst.1.2.1, e.snd.1.1.1, e.snd.1.2.1)) hcd
  by_cases hc : Even (c.1.1 + c.2.1) <;>
    by_cases hd : Even (d.1.1 + d.2.1) <;>
    simp [fkIsingSquareRadialPatchCellDualDart,
      fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead, hc, hd] at hcoords <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

theorem fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation_eq_cellDarts
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (c : FKIsingSquareRadialPatchInteriorCell m) :
    fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
        n m hn hm hmpos c.1.1 c.2.1 =
      |fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base
          (fkIsingSquareRadialPatchCellPrimalDart n m hm c).snd -
        fkIsingSquareRadialPatchPrimalValue n m hn hm hmpos base
          (fkIsingSquareRadialPatchCellPrimalDart n m hm c).fst| +
      |fkIsingSquareRadialPatchDualValue n m hn hm hmpos base
          (fkIsingSquareRadialPatchCellDualDart m c).snd -
        fkIsingSquareRadialPatchDualValue n m hn hm hmpos base
          (fkIsingSquareRadialPatchCellDualDart m c).fst| := by
  classical
  by_cases h : Even (c.1.1 + c.2.1)
  · simp [fkIsingSquareRadialPatchCellPrimalDart,
      fkIsingSquareRadialPatchCellDualDart,
      fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead,
      fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead, h]
    unfold fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
    unfold fkIsingSquareRadialPatchPrimalValue
      fkIsingSquareRadialPatchDualValue
    simp
  · simp [fkIsingSquareRadialPatchCellPrimalDart,
      fkIsingSquareRadialPatchCellDualDart,
      fkIsingSquareRadialPatchCellPrimalTail,
      fkIsingSquareRadialPatchCellPrimalHead,
      fkIsingSquareRadialPatchCellDualTail,
      fkIsingSquareRadialPatchCellDualHead, h]
    unfold fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
    unfold fkIsingSquareRadialPatchPrimalValue
      fkIsingSquareRadialPatchDualValue
    simp
    rw [abs_sub_comm
      (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos
        c.1.1 (c.2.1 + 1))
      (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos
        (c.1.1 + 1) c.2.1)]
    ring


end
end StatMech.Universality
