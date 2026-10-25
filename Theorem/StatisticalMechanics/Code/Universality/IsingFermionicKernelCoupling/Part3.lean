/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part4


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem isingLeapfrogKilledKernel_eq_natCard_choicePath_div
    (R t : Nat) (p q : IsingLeapfrogBox R) :
    isingLeapfrogKilledKernel R t p q =
      Nat.card (IsingLeapfrogKilledChoicePathFamily R t p q) /
        (4 : Real) ^ t := by
  induction t generalizing p with
  | zero =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · have hempty :
            ∀ w : IsingLeapfrogKilledChoicePathFamily R 0 p q, False := by
          intro w
          have hfinal := w.2.2.1.endpoint_not_boundary R p w.1
          have : ¬ isingLeapfrogBoxBoundary R q := by
            simpa [w.2.2.2] using hfinal
          exact this hq
        rw [Nat.card_congr
          (killedChoicePathFamilyEmptyEquiv R 0 p q hempty)]
        simp [isingLeapfrogKilledKernel, hq]
      · by_cases hpq : p = q
        · subst q
          rw [Nat.card_congr (killedChoicePathFamilyZeroSelfEquiv R p hq)]
          simp [isingLeapfrogKilledKernel, hq, isingLeapfrogStoppedKernel]
        · rw [Nat.card_congr (killedChoicePathFamilyEmptyEquiv R 0 p q
              (fun w => hpq (by
                have hnil : w.1 = [] :=
                  List.eq_nil_of_length_eq_zero w.2.1
                simpa [hnil, isingLeapfrogChoiceRun] using w.2.2.2)))]
          simp [isingLeapfrogKilledKernel, hq, isingLeapfrogStoppedKernel,
            hpq]
  | succ t ih =>
      by_cases hq : isingLeapfrogBoxBoundary R q
      · have hempty :
            ∀ w : IsingLeapfrogKilledChoicePathFamily R (t + 1) p q,
              False := by
          intro w
          have hfinal := w.2.2.1.endpoint_not_boundary R p w.1
          have : ¬ isingLeapfrogBoxBoundary R q := by
            simpa [w.2.2.2] using hfinal
          exact this hq
        rw [Nat.card_congr
          (killedChoicePathFamilyEmptyEquiv R (t + 1) p q hempty)]
        simp [isingLeapfrogKilledKernel, hq]
      · by_cases hp : isingLeapfrogBoxBoundary R p
        · rw [Nat.card_congr (killedChoicePathFamilyEmptyEquiv R (t + 1)
              p q (fun w =>
                w.2.2.1.start_not_boundary R p w.1 hp))]
          simp [isingLeapfrogKilledKernel, hq,
            isingLeapfrogStoppedKernel_of_boundary R (t + 1) p q hp,
            show p ≠ q from fun hpq => hq (hpq ▸ hp)]
        · rw [Nat.card_congr
              (killedChoicePathFamilySuccEquiv R t p q hp),
            Nat.card_sigma, Fintype.sum_prod_type]
          simp only [isingLeapfrogKilledKernel, if_neg hq,
            isingLeapfrogStoppedKernel, dif_neg hp,
            isingLeapfrogChoiceNext, hp, ↓reduceDIte]
          have hSW := ih (isingLeapfrogSW R p)
          have hSE := ih (isingLeapfrogSE R p hp)
          have hNW := ih (isingLeapfrogNW R p hp)
          have hNE := ih (isingLeapfrogNE R p hp)
          simp only [isingLeapfrogKilledKernel, if_neg hq] at hSW hSE hNW hNE
          rw [hSW, hSE, hNW, hNE]
          simp
          push_cast
          rw [pow_succ]
          ring

end
end StatMech.Universality
