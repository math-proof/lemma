/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingLeapfrogChoiceNoHitAll_finite
    (t : Nat) (start level : Int) :
    Finite (IsingLeapfrogChoiceNoHitAll t start level) := by
  exact Finite.of_injective
    (fun w : IsingLeapfrogChoiceNoHitAll t start level => w.1)
    Subtype.val_injective

end
end StatMech.Universality
