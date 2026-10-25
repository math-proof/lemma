/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance localHorizontalHitFiber_finite
    (t : Nat) (start level target : Int) :
    Finite (LocalHorizontalHitFiber t start level target) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance localHorizontalNoHitFiber_finite
    (t : Nat) (start level target : Int) :
    Finite (LocalHorizontalNoHitFiber t start level target) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

end
end StatMech.Universality
