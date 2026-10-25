/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem isingLeapfrogStoppedKernel_eq_natCard_choicePath_div
    (R t : Nat) (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R t p q =
      Nat.card (IsingLeapfrogStoppedChoicePathFamily R t p q) /
        (4 : Real) ^ t := by
  induction t generalizing p with
  | zero =>
      by_cases hpq : p = q
      · subst q
        rw [Nat.card_congr (stoppedChoicePathFamilyZeroSelfEquiv R p)]
        simp [isingLeapfrogStoppedKernel]
      · rw [Nat.card_congr
          (stoppedChoicePathFamilyZeroNeEquiv R p q hpq)]
        simp [isingLeapfrogStoppedKernel, hpq]
  | succ t ih =>
      rw [isingLeapfrogStoppedKernel_succ]
      rw [Nat.card_congr (stoppedChoicePathFamilySuccEquiv R t p q),
        Nat.card_sigma, Fintype.sum_prod_type]
      by_cases hp : isingLeapfrogBoxBoundary R p
      · simp only [dif_pos hp, isingLeapfrogChoiceNext, hp, ↓reduceDIte]
        rw [ih]
        simp
        rw [pow_succ]
        ring
      · simp only [dif_neg hp, isingLeapfrogChoiceNext, hp, ↓reduceDIte]
        rw [ih, ih, ih, ih]
        simp
        push_cast
        rw [pow_succ]
        ring


end
end StatMech.Universality
