/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9


namespace StatMech.Universality

open Finset

noncomputable section

theorem IsingLeapfrogDiffusiveExitInputs.kernelInputs
    {A B : Real} (hAB : IsingLeapfrogDiffusiveExitInputs A B) :
    IsingLeapfrogDiffusiveKernelInputs (A + 4) B := by
  refine ⟨add_nonneg hAB.1 (by norm_num), hAB.2.1, ?_⟩
  intro R ρ p p' hρ hp hp' hpp'
  have hinputs := hAB.2.2 R ρ p p' hρ hp hp' hpp'
  refine ⟨?_, hinputs.2⟩
  intro q
  rw [isingLeapfrogStoppedKernel_eq_killed_add_exit R (ρ * ρ) p q,
    isingLeapfrogStoppedKernel_eq_killed_add_exit
      R (ρ * ρ + 1) p' q]
  calc
    |(isingLeapfrogKilledKernel R (ρ * ρ) p q +
          isingLeapfrogExitKernel R (ρ * ρ) p q) -
        (isingLeapfrogKilledKernel R (ρ * ρ + 1) p' q +
          isingLeapfrogExitKernel R (ρ * ρ + 1) p' q)| =
        |(isingLeapfrogKilledKernel R (ρ * ρ) p q -
            isingLeapfrogKilledKernel R (ρ * ρ + 1) p' q) +
          (isingLeapfrogExitKernel R (ρ * ρ) p q -
            isingLeapfrogExitKernel R (ρ * ρ + 1) p' q)| := by
      congr 1
      ring
    _ ≤ |isingLeapfrogKilledKernel R (ρ * ρ) p q -
          isingLeapfrogKilledKernel R (ρ * ρ + 1) p' q| +
        |isingLeapfrogExitKernel R (ρ * ρ) p q -
          isingLeapfrogExitKernel R (ρ * ρ + 1) p' q| :=
      abs_add_le _ _
    _ ≤ 4 / (ρ : Real) ^ 2 + A / (ρ : Real) ^ 2 :=
      add_le_add
        (isingLeapfrogKilledKernel_diffusive_abs_sub_le R ρ p p' q hρ)
        (hinputs.1 q)
    _ = (A + 4) / (ρ : Real) ^ 2 := by ring

theorem IsingLeapfrogDiffusiveExitInputs.gradientBound
    {A B : Real} (hAB : IsingLeapfrogDiffusiveExitInputs A B) :
    IsingLeapfrogDiffusiveGradientBound ((A + 4) * B) :=
  hAB.kernelInputs.gradientBound

end
end StatMech.Universality
