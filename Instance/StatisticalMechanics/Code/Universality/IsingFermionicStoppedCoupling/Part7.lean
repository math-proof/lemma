/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part14


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingLeapfrogHorizontalEscapeFamily_finite
    (n t : Nat) : Finite (IsingLeapfrogHorizontalEscapeFamily n t) := by
  exact Finite.of_injective
    (fun w : IsingLeapfrogHorizontalEscapeFamily n t => w.1)
    Subtype.val_injective

end
end StatMech.Universality
