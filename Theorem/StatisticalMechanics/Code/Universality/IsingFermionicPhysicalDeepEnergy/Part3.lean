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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatch_deepCellDiagonalVariation_sum_le
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (base : Real) :
    (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
          n m hn hm (by omega) c.1.1 c.2.1) ≤
      (∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
        |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
      ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
        |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
          fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst| := by
  classical
  let C := fkIsingSquareRadialPatchDeepCells n m hm hm2 r
  let Sp := fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r
  let Sd := fkIsingSquareRadialPatchDualDeepDarts m hm2 r
  let pd := fkIsingSquareRadialPatchCellPrimalDart n m hm
  let dd := fkIsingSquareRadialPatchCellDualDart m
  let fp := fun d : (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart ↦
    |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
      fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|
  let fd := fun d : (fkIsingSquareRadialPatchDualGraph m).Dart ↦
    |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
      fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|
  have hpInject : Set.InjOn pd (C : Set _) :=
    (fkIsingSquareRadialPatchCellPrimalDart_injective n m hm).injOn
  have hdInject : Set.InjOn dd (C : Set _) :=
    (fkIsingSquareRadialPatchCellDualDart_injective m).injOn
  have hpSubset : C.image pd ⊆ Sp := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp hc).2.1
  have hdSubset : C.image dd ⊆ Sd := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp hc).2.2
  have hpSum : (∑ c ∈ C, fp (pd c)) ≤ ∑ d ∈ Sp, fp d := by
    rw [← Finset.sum_image hpInject]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpSubset
      (fun d _ _ ↦ abs_nonneg _)
  have hdSum : (∑ c ∈ C, fd (dd c)) ≤ ∑ d ∈ Sd, fd d := by
    rw [← Finset.sum_image hdInject]
    exact Finset.sum_le_sum_of_subset_of_nonneg hdSubset
      (fun d _ _ ↦ abs_nonneg _)
  simp_rw [fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation_eq_cellDarts
    n m hn hm (by omega) base]
  change (∑ c ∈ C, (fp (pd c) + fd (dd c))) ≤ _
  rw [Finset.sum_add_distrib]
  exact add_le_add hpSum hdSum


theorem fkIsingSquareRadialPatch_deepCell_normSq_sum_le_variation
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (base : Real) :
    (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
        Complex.normSq
          (fkIsingSquareRadialPatchFullObservable n m hn hm
            ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) ≤
      2 *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
          |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
  have hcell :
      (∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) ≤
        2 *
          ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
            fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
              n m hn hm (by omega) c.1.1 c.2.1 := by
    calc
      _ ≤ ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          2 * fkIsingSquareRadialPatchPrimitiveCellDiagonalVariation
            n m hn hm (by omega) c.1.1 c.2.1 := by
        apply Finset.sum_le_sum
        intro c hc
        exact fkIsingSquareRadialPatch_normSq_full_le_two_mul_cellDiagonalVariation
          n m hn hm (by omega) ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩
      _ = _ := by simp_rw [Finset.mul_sum]
  have hvariation :=
    fkIsingSquareRadialPatch_deepCellDiagonalVariation_sum_le
      n m hn hm hm2 r base
  exact hcell.trans (mul_le_mul_of_nonneg_left hvariation (by norm_num))


theorem fkIsingSquareRadialPatch_deepCell_physicalNormalized_energy_le
    (n m : Nat) (mesh : Real) (hn : 0 < n) (hm : m ≤ n)
    (hm2 : 2 ≤ m) (hmesh : 0 < mesh) (r : Nat) (base : Real) :
    mesh ^ 2 *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
                ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩ /
              (Real.sqrt (2 * mesh) : Complex)) ≤
      mesh *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
          |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|) := by
  have hsqrtSq : Real.sqrt (2 * mesh) ^ 2 = 2 * mesh := by
    rw [Real.sq_sqrt]
    positivity
  have hnorm (z : Complex) :
      Complex.normSq (z / (Real.sqrt (2 * mesh) : Complex)) =
        Complex.normSq z / (2 * mesh) := by
    rw [Complex.normSq_div]
    congr 1
    rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by positivity))]
    exact hsqrtSq
  have hraw := fkIsingSquareRadialPatch_deepCell_normSq_sum_le_variation
    n m hn hm hm2 r base
  simp_rw [hnorm]
  rw [← Finset.sum_div]
  calc
    mesh ^ 2 *
        ((∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩)) / (2 * mesh)) =
      mesh / 2 *
        ∑ c ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r,
          Complex.normSq
            (fkIsingSquareRadialPatchFullObservable n m hn hm
              ⟨c.1.1, by omega⟩ ⟨c.2.1, by omega⟩) := by
        field_simp
    _ ≤ mesh / 2 * (2 *
        ((∑ d ∈ fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r,
          |fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchPrimalValue n m hn hm (by omega) base d.fst|) +
        ∑ d ∈ fkIsingSquareRadialPatchDualDeepDarts m hm2 r,
          |fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.snd -
            fkIsingSquareRadialPatchDualValue n m hn hm (by omega) base d.fst|)) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = _ := by ring

end
end StatMech.Universality
