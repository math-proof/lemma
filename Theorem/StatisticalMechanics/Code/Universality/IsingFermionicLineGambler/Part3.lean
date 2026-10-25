/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part17
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part5


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLineStoppedKernel_eq_natCard_choicePath_div (n t : Nat)
    (p q : IsingLineBox n) :
    isingLineStoppedKernel n t p q =
      Nat.card (IsingLineChoicePathFamily n t p q) / (2 : Real) ^ t := by
  induction t generalizing p with
  | zero =>
      by_cases hpq : p = q
      · subst q
        rw [Nat.card_congr (isingLineChoicePathFamilyZeroSelfEquiv n p)]
        simp [isingLineStoppedKernel]
      · rw [Nat.card_congr
          (isingLineChoicePathFamilyZeroNeEquiv n p q hpq)]
        simp [isingLineStoppedKernel, hpq]
  | succ t ih =>
      rw [show isingLineStoppedKernel n (t + 1) p q =
          if hp : isingLineBoxBoundary n p then
            isingLineStoppedKernel n t p q
          else
            (isingLineStoppedKernel n t (isingLineWest n p) q +
              isingLineStoppedKernel n t (isingLineEast n p hp) q) / 2 by
        rfl]
      rw [Nat.card_congr (isingLineChoicePathFamilySuccEquiv n t p q),
        Nat.card_sigma]
      by_cases hp : isingLineBoxBoundary n p
      · simp only [dif_pos hp, isingLineChoiceNext, hp, ↓reduceDIte]
        rw [ih]
        simp
        rw [pow_succ]
        ring
      · simp only [dif_neg hp, isingLineChoiceNext, hp, ↓reduceDIte]
        rw [ih, ih]
        simp
        push_cast
        rw [pow_succ]
        ring

end
end StatMech.Universality
