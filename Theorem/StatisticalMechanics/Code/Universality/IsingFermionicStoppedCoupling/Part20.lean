/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part24


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem sourceFailureReflectX_injective
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Nat)
    (hlevelR : level ≤ R) :
    Function.Injective (sourceFailureReflectX R t p level hlevelR) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact flipXChoices_injective (congrArg (fun z => z.1.1) h)

end
end StatMech.Universality
