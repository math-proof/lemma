/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part4


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance isingHorizontalNoHitEndpointFamily_finite
    (t : Nat) (level target : Int) :
    Finite (IsingHorizontalNoHitEndpointFamily t level target) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

end
end StatMech.Universality
