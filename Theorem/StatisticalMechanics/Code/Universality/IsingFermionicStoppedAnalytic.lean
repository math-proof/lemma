/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedAnalytic


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

@[simp] theorem isingLeapfrogBoxSwap_involutive (R : Nat)
    (p : IsingLeapfrogBox R) :
    isingLeapfrogBoxSwap R (isingLeapfrogBoxSwap R p) = p := rfl

@[simp] theorem isingLeapfrogBoxSwap_eq_iff (R : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogBoxSwap R p = isingLeapfrogBoxSwap R q ↔ p = q :=
  (Function.Involutive.injective
    (isingLeapfrogBoxSwap_involutive R)).eq_iff

end
end StatMech.Universality
