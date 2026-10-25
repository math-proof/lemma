/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance horizontalHitBelow_finite
    (t : Nat) (start level : Int) :
    Finite (HorizontalHitBelow t start level) := by
  exact Finite.of_injective
    (fun z : HorizontalHitBelow t start level => z.1)
    (by
      intro a b h
      exact Subtype.ext h)


end
end StatMech.Universality
