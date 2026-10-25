/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6


namespace StatMech.Universality

open Finset

noncomputable section

theorem IsingLeapfrogDiffusiveKernelInputs.gradientBound
    {A B : Real} (hAB : IsingLeapfrogDiffusiveKernelInputs A B) :
    IsingLeapfrogDiffusiveGradientBound (A * B) := by
  refine ⟨mul_nonneg hAB.1 hAB.2.1, ?_⟩
  intro R ρ p p' hρ hp hp' hpp'
  have hinputs := hAB.2.2 R ρ p p' hρ hp hp' hpp'
  calc
    isingLeapfrogStoppedKernelTimeGradientSq R
        (ρ * ρ) (ρ * ρ + 1) p p' ≤
        (A / (ρ : Real) ^ 2) *
          ∑ q, |isingLeapfrogStoppedKernel R (ρ * ρ) p q -
            isingLeapfrogStoppedKernel R (ρ * ρ + 1) p' q| :=
      isingLeapfrogStoppedKernelTimeGradientSq_le_mul_l1
        R (ρ * ρ) (ρ * ρ + 1) p p'
        (A / (ρ : Real) ^ 2) hinputs.1
    _ ≤ (A / (ρ : Real) ^ 2) * (B / (ρ : Real)) := by
      exact mul_le_mul_of_nonneg_left hinputs.2 (div_nonneg hAB.1 (by positivity))
    _ = A * B / (ρ : Real) ^ 3 := by
      have hρR : (ρ : Real) ≠ 0 := by positivity
      field_simp


theorem isingLeapfrogDiffusiveGradientBound_unitMargin
    (R : Nat) (p p' : IsingLeapfrogBox R)
    (_hp : IsingLeapfrogInteriorMargin R 1 p)
    (_hp' : IsingLeapfrogInteriorMargin R 1 p')
    (_hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    isingLeapfrogStoppedKernelTimeGradientSq R 1 2 p p' ≤
      (2 : Real) / (1 : Real) ^ 3 := by
  simpa using isingLeapfrogStoppedKernelTimeGradientSq_le_two R 1 2 p p'


theorem IsingLeapfrogHarmonicOnBox.normSq_sub_le_of_diffusiveGradient
    {C : Real} (hC : IsingLeapfrogDiffusiveGradientBound C)
    {R ρ : Nat} {f : IsingLeapfrogBox R → Complex}
    (hf : IsingLeapfrogHarmonicOnBox R f)
    (p p' : IsingLeapfrogBox R) (hρ : 0 < ρ)
    (hp : IsingLeapfrogInteriorMargin R ρ p)
    (hp' : IsingLeapfrogInteriorMargin R ρ p')
    (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
    Complex.normSq (f p - f p') ≤
      (C / (ρ : Real) ^ 3) * ∑ q, Complex.normSq (f q) := by
  refine le_trans (hf.normSq_sub_le_kernelTimeGradient
    (ρ * ρ) (ρ * ρ + 1) p p') ?_
  exact mul_le_mul_of_nonneg_right
    (hC.2 R ρ p p' hρ hp hp' hpp')
    (Finset.sum_nonneg fun q _ ↦ Complex.normSq_nonneg (f q))


end
end StatMech.Universality
