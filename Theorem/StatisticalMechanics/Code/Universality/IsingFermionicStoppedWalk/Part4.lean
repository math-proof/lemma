/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part5


namespace StatMech.Universality

open Finset

noncomputable section

@[simp] theorem isingLeapfrogStoppedKernelTimeGradientSq_sameTime
    (R t : Nat) (p p' : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernelTimeGradientSq R t t p p' =
      isingLeapfrogStoppedKernelGradientSq R t p p' := rfl


theorem isingLeapfrogStoppedKernelTimeGradientSq_le_two
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' ≤ 2 := by
  classical
  unfold isingLeapfrogStoppedKernelTimeGradientSq
  calc
    _ ≤ ∑ q, (isingLeapfrogStoppedKernel R t p q +
        isingLeapfrogStoppedKernel R t' p' q) := by
      apply Finset.sum_le_sum
      intro q hq
      have ha0 := isingLeapfrogStoppedKernel_nonneg R t p q
      have ha1 := isingLeapfrogStoppedKernel_le_one R t p q
      have hb0 := isingLeapfrogStoppedKernel_nonneg R t' p' q
      have hb1 := isingLeapfrogStoppedKernel_le_one R t' p' q
      nlinarith [mul_nonneg ha0 hb0]
    _ = (∑ q, isingLeapfrogStoppedKernel R t p q) +
        ∑ q, isingLeapfrogStoppedKernel R t' p' q := by
      rw [Finset.sum_add_distrib]
    _ = 2 := by
      rw [isingLeapfrogStoppedKernel_sum_eq_one,
        isingLeapfrogStoppedKernel_sum_eq_one]
      norm_num


theorem isingLeapfrogStoppedKernelTimeGradientSq_le_mul_l1
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) (A : Real)
    (hpoint : ∀ q, |isingLeapfrogStoppedKernel R t p q -
      isingLeapfrogStoppedKernel R t' p' q| ≤ A) :
    isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' ≤
      A * ∑ q, |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t' p' q| := by
  classical
  unfold isingLeapfrogStoppedKernelTimeGradientSq
  calc
    _ ≤ ∑ q, A * |isingLeapfrogStoppedKernel R t p q -
        isingLeapfrogStoppedKernel R t' p' q| := by
      apply Finset.sum_le_sum
      intro q hq
      rw [← sq_abs, pow_two]
      exact mul_le_mul_of_nonneg_right (hpoint q) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]


theorem IsingLeapfrogHarmonicOnBox.normSq_sub_le_kernelGradient
    {R : Nat} {f : IsingLeapfrogBox R → Complex}
    (hf : IsingLeapfrogHarmonicOnBox R f) (t : Nat)
    (p p' : IsingLeapfrogBox R) :
    Complex.normSq (f p - f p') ≤
      isingLeapfrogStoppedKernelGradientSq R t p p' *
        ∑ q, Complex.normSq (f q) := by
  classical
  rw [← hf.stoppedMean_eq t p, ← hf.stoppedMean_eq t p']
  unfold isingLeapfrogStoppedMean isingLeapfrogStoppedKernelGradientSq
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  have hcs := isingComplex_normSq_sum_mul_le Finset.univ
    (fun q ↦ isingLeapfrogStoppedKernel R t p q -
      isingLeapfrogStoppedKernel R t p' q) f
  convert hcs using 1 <;> simp


theorem IsingLeapfrogHarmonicOnBox.normSq_sub_le_kernelTimeGradient
    {R : Nat} {f : IsingLeapfrogBox R → Complex}
    (hf : IsingLeapfrogHarmonicOnBox R f) (t t' : Nat)
    (p p' : IsingLeapfrogBox R) :
    Complex.normSq (f p - f p') ≤
      isingLeapfrogStoppedKernelTimeGradientSq R t t' p p' *
        ∑ q, Complex.normSq (f q) := by
  classical
  rw [← hf.stoppedMean_eq t p, ← hf.stoppedMean_eq t' p']
  unfold isingLeapfrogStoppedMean isingLeapfrogStoppedKernelTimeGradientSq
  rw [← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  have hcs := isingComplex_normSq_sum_mul_le Finset.univ
    (fun q ↦ isingLeapfrogStoppedKernel R t p q -
      isingLeapfrogStoppedKernel R t' p' q) f
  convert hcs using 1 <;> simp


end
end StatMech.Universality
