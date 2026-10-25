/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiamondIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveFiniteIntegration
import Def.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration
open Finset


namespace StatMech.Universality

noncomputable section

theorem isingCenteredSum_self (f : Nat → Real) (center : Nat) :
    isingCenteredSum f center center = 0 := by
  simp [isingCenteredSum]

theorem isingCenteredSum_succ_sub
    (f : Nat → Real) (center i : Nat) :
    isingCenteredSum f center (i + 1) - isingCenteredSum f center i = f i := by
  by_cases hci : center ≤ i
  · have hci' : center ≤ i + 1 := by omega
    rw [isingCenteredSum, if_pos hci', isingCenteredSum, if_pos hci]
    rw [Finset.sum_Ico_succ_top hci]
    ring
  · by_cases hi : i + 1 = center
    · subst center
      simp [isingCenteredSum]
    · have hlt : i + 1 < center := by omega
      rw [isingCenteredSum, if_neg (by omega),
        isingCenteredSum, if_neg (by omega)]
      have hs := Finset.sum_Ico_sub_bot f (show i < center by omega)
      linarith

end
end StatMech.Universality
