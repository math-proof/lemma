/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem IsingLeapfrogHarmonicOnBox.norm_sub_le_kernelTimeL1
    {R : Nat} {f : IsingLeapfrogBox R → Complex}
    (hf : IsingLeapfrogHarmonicOnBox R f) (B : Real)
    (hB : ∀ q, ‖f q‖ ≤ B) (t t' : Nat)
    (p p' : IsingLeapfrogBox R) :
    ‖f p - f p'‖ ≤
      B * ∑ q, |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t' p' q| := by
  classical
  rw [← hf.stoppedMean_eq t p, ← hf.stoppedMean_eq t' p']
  unfold isingLeapfrogStoppedMean
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  calc
    ‖∑ q, ((isingLeapfrogStoppedKernel R t p q : Complex) -
          isingLeapfrogStoppedKernel R t' p' q) * f q‖ ≤
        ∑ q, ‖((isingLeapfrogStoppedKernel R t p q : Complex) -
          isingLeapfrogStoppedKernel R t' p' q) * f q‖ :=
      norm_sum_le _ _
    _ = ∑ q, |isingLeapfrogStoppedKernel R t p q -
          isingLeapfrogStoppedKernel R t' p' q| * ‖f q‖ := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [norm_mul, show
        ((isingLeapfrogStoppedKernel R t p q : Complex) -
            isingLeapfrogStoppedKernel R t' p' q) =
          ((isingLeapfrogStoppedKernel R t p q -
            isingLeapfrogStoppedKernel R t' p' q : Real) : Complex) by
          norm_num,
        Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ q, |isingLeapfrogStoppedKernel R t p q -
          isingLeapfrogStoppedKernel R t' p' q| * B := by
      apply Finset.sum_le_sum
      intro q _hq
      exact mul_le_mul_of_nonneg_left (hB q) (abs_nonneg _)
    _ = B * ∑ q, |isingLeapfrogStoppedKernel R t p q -
          isingLeapfrogStoppedKernel R t' p' q| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      ring


theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_norm_le_two
    (n : Nat) (hn : 0 < n) (i j : Fin (2 * n)) :
    ‖fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j‖ ≤ 2 := by
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  let e := fkIsingSquareCenteredRadialPatchEdge n i j
  change ‖D.fermionicObservable (.dart (e, .west)) +
      D.fermionicObservable (.dart (e, .east))‖ ≤ 2
  calc
    _ ≤ ‖D.fermionicObservable (.dart (e, .west))‖ +
        ‖D.fermionicObservable (.dart (e, .east))‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add
      (D.norm_fermionicObservable_le_one _)
      (D.norm_fermionicObservable_le_one _)
    _ = 2 := by norm_num


theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_leapfrog_harmonic
    (n i j : Nat) (hn : 0 < n)
    (hi : i + 3 < 2 * n) (hj : j + 3 < 2 * n) :
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j + 2, by omega⟩ +
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i + 2, by omega⟩ ⟨j, by omega⟩ +
        fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ =
      4 * fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ := by
  have hSW :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
      n i j hn (by omega) (by omega)
  have hSE :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
      n (i + 1) j hn (by omega) (by omega)
  have hNW :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
      n i (j + 1) hn (by omega) (by omega)
  have hNE :=
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
      n (i + 1) (j + 1) hn (by omega) (by omega)
  have h := isingCellCRAt_leapfrog_harmonic
    (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn)
    i j hSW hSE hNW hNE
  simpa [fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension,
    show i < 2 * n by omega, show j < 2 * n by omega,
    show i + 1 < 2 * n by omega, show j + 1 < 2 * n by omega,
    show i + 2 < 2 * n by omega, show j + 2 < 2 * n by omega] using h


end
end StatMech.Universality
