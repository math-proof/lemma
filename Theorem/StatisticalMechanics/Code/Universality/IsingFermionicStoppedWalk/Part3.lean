/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part4


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLeapfrogStoppedBoundaryMass_nonneg (R t : Nat)
    (p : IsingLeapfrogBox R) :
    0 ≤ isingLeapfrogStoppedBoundaryMass R t p := by
  classical
  unfold isingLeapfrogStoppedBoundaryMass
  exact Finset.sum_nonneg fun q _ ↦
    isingLeapfrogStoppedKernel_nonneg R t p q

@[simp] theorem isingLeapfrogStoppedBoundaryMass_zero (R : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedBoundaryMass R 0 p =
      if isingLeapfrogBoxBoundary R p then 1 else 0 := by
  classical
  unfold isingLeapfrogStoppedBoundaryMass isingLeapfrogStoppedKernel
  by_cases hp : isingLeapfrogBoxBoundary R p
  · simp [hp]
  · simp [hp]

theorem isingLeapfrogStoppedBoundaryMass_succ (R t : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedBoundaryMass R (t + 1) p =
      if hp : isingLeapfrogBoxBoundary R p then
        isingLeapfrogStoppedBoundaryMass R t p
      else
        (isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogSW R p) +
          isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogSE R p hp) +
          isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogNW R p hp) +
          isingLeapfrogStoppedBoundaryMass R t (isingLeapfrogNE R p hp)) / 4 := by
  classical
  unfold isingLeapfrogStoppedBoundaryMass
  by_cases hp : isingLeapfrogBoxBoundary R p
  · simp [isingLeapfrogStoppedKernel, hp]
  · simp only [isingLeapfrogStoppedKernel, dif_neg hp]
    rw [← Finset.sum_div]
    repeat' rw [Finset.sum_add_distrib]


theorem isingLeapfrogStoppedBoundaryMass_mono (R t : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedBoundaryMass R t p ≤
      isingLeapfrogStoppedBoundaryMass R (t + 1) p := by
  induction t generalizing p with
  | zero =>
      rw [isingLeapfrogStoppedBoundaryMass_succ]
      split_ifs with hp
      · exact le_rfl
      · simp [hp]
        positivity
  | succ t ih =>
      rw [isingLeapfrogStoppedBoundaryMass_succ,
        isingLeapfrogStoppedBoundaryMass_succ]
      split_ifs with hp
      · exact ih p
      · have hSW := ih (isingLeapfrogSW R p)
        have hSE := ih (isingLeapfrogSE R p hp)
        have hNW := ih (isingLeapfrogNW R p hp)
        have hNE := ih (isingLeapfrogNE R p hp)
        linarith


theorem IsingLeapfrogHarmonicOnBox.stoppedMean_eq
    {R : Nat} {f : IsingLeapfrogBox R → Complex}
    (hf : IsingLeapfrogHarmonicOnBox R f) (t : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogStoppedMean R t f p = f p := by
  induction t generalizing p with
  | zero => exact isingLeapfrogStoppedMean_zero R f p
  | succ t ih =>
      rw [isingLeapfrogStoppedMean_succ]
      split_ifs with hp
      · exact ih p
      · rw [ih, ih, ih, ih]
        have h := hf p hp
        apply (div_eq_iff (by norm_num : (4 : Complex) ≠ 0)).2
        linear_combination h


end
end StatMech.Universality
