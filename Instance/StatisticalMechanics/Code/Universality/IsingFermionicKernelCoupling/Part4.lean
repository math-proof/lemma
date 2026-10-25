/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Def.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part9


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingLeapfrogKilledChoiceNoHitFamily_finite
    (R t : Nat) (p q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingLeapfrogKilledChoiceNoHitFamily R t p q level) :=
  Finite.of_injective Subtype.val Subtype.val_injective

end
end StatMech.Universality
