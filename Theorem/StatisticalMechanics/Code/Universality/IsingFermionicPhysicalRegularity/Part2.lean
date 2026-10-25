/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
import Mathlib.Data.Nat.Choose.Vandermonde
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

open Finset


@[simp] theorem fkIsingSquareRadialPatchFullObservableExtension_apply
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n)
    (i j : Nat) (hi : i < m) (hj : j < m) :
    fkIsingSquareRadialPatchFullObservableExtension n m hn hm i j =
      fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [fkIsingSquareRadialPatchFullObservableExtension, hi, hj]


theorem fkIsingSquareRadialPatchFullObservable_cellCR
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi : i + 2 < m) (hj : j + 2 < m) :
    IsingCellCRAt
      (fkIsingSquareRadialPatchFullObservableExtension n m hn hm) i j := by
  by_cases heven : Even (i + 1 + (j + 1))
  · have hquad := fkIsingSquareRadialPatchFullObservable_quad
      n m (i + 1) (j + 1) hn hm (by omega) (by omega)
      (by omega) (by omega) heven
    unfold IsingCellCRAt fkIsingSquareRadialPatchFullObservableExtension
    simp [show i < m by omega, show i + 1 < m by omega,
      show j < m by omega, show j + 1 < m by omega]
    simpa using hquad.2.2
  · have hquad := fkIsingSquareRadialPatchFullObservable_quad_of_odd
      n m (i + 1) (j + 1) hn hm (by omega) (by omega)
      (by omega) (by omega) heven
    unfold IsingCellCRAt fkIsingSquareRadialPatchFullObservableExtension
    simp [show i < m by omega, show i + 1 < m by omega,
      show j < m by omega, show j + 1 < m by omega]
    have h := hquad.2.2
    simp only [Nat.add_sub_cancel] at h
    linear_combination -h


theorem fkIsingSquareRadialPatchFullObservable_leapfrog_harmonic
    (n m i j : Nat) (hn : 0 < n) (hm : m ≤ n)
    (hi : i + 3 < m) (hj : j + 3 < m) :
    fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i, by omega⟩ ⟨j + 2, by omega⟩ +
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i + 2, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareRadialPatchFullObservable n m hn hm
          ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ =
      4 * fkIsingSquareRadialPatchFullObservable n m hn hm
        ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ := by
  have hSW := fkIsingSquareRadialPatchFullObservable_cellCR
      n m i j hn hm (by omega) (by omega)
  have hSE := fkIsingSquareRadialPatchFullObservable_cellCR
      n m (i + 1) j hn hm (by omega) (by omega)
  have hNW := fkIsingSquareRadialPatchFullObservable_cellCR
      n m i (j + 1) hn hm (by omega) (by omega)
  have hNE := fkIsingSquareRadialPatchFullObservable_cellCR
      n m (i + 1) (j + 1) hn hm (by omega) (by omega)
  have h := isingCellCRAt_leapfrog_harmonic
    (fkIsingSquareRadialPatchFullObservableExtension n m hn hm) i j
    hSW hSE hNW hNE
  simpa [fkIsingSquareRadialPatchFullObservableExtension,
    show i < m by omega, show j < m by omega,
    show i + 1 < m by omega, show j + 1 < m by omega,
    show i + 2 < m by omega, show j + 2 < m by omega] using h


theorem isingCentralBinom_sq_mul_le (n : Nat) :
    ((Nat.centralBinom n : Real) ^ 2) * (2 * n + 1) ≤ (16 : Real) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hrecNat := Nat.succ_mul_centralBinom_succ n
      have hrec := congrArg (fun k : Nat ↦ (k : Real)) hrecNat
      push_cast at hrec
      rw [pow_succ]
      have hfac : 0 ≤ 4 * (2 * (n : Real) + 3) * (2 * (n : Real) + 1) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_left ih hfac
      have hpoly :
          4 * (2 * (n : Real) + 3) * (2 * (n : Real) + 1) ≤
            16 * ((n : Real) + 1) ^ 2 := by nlinarith
      have hpow : 0 ≤ (16 : Real) ^ n := by positivity
      have hrecSq := congrArg (fun x : Real ↦ x ^ 2) hrec
      change (((n : Real) + 1) *
          (Nat.centralBinom (n + 1) : Real)) ^ 2 =
        (2 * (2 * (n : Real) + 1) * Nat.centralBinom n) ^ 2 at hrecSq
      have hmain :
          ((n : Real) + 1) ^ 2 *
              (((Nat.centralBinom (n + 1) : Real) ^ 2) *
                (2 * (n + 1 : Nat) + 1)) ≤
            ((n : Real) + 1) ^ 2 * (16 * (16 : Real) ^ n) := by
        calc
          _ = (((n : Real) + 1) *
                (Nat.centralBinom (n + 1) : Real)) ^ 2 *
                (2 * (n : Real) + 3) := by
              push_cast
              ring
          _ = (2 * (2 * (n : Real) + 1) *
                Nat.centralBinom n) ^ 2 * (2 * (n : Real) + 3) := by
              rw [hrecSq]
          _ = (4 * (2 * (n : Real) + 3) * (2 * (n : Real) + 1)) *
                (((Nat.centralBinom n : Real) ^ 2) *
                  (2 * (n : Real) + 1)) := by ring
          _ ≤ (4 * (2 * (n : Real) + 3) * (2 * (n : Real) + 1)) *
                (16 : Real) ^ n := hmul
          _ ≤ (16 * ((n : Real) + 1) ^ 2) * (16 : Real) ^ n :=
            mul_le_mul_of_nonneg_right hpoly hpow
          _ = _ := by ring
      have hmain' := (by
        simpa only [Nat.cast_add, Nat.cast_one] using hmain)
      have hcancel := le_of_mul_le_mul_left hmain'
        (show 0 < ((n : Real) + 1) ^ 2 by positivity)
      convert hcancel using 1 <;> push_cast <;> ring


end
end StatMech.Universality
