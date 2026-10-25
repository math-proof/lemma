/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part4


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem lineFreeEndpoint_choiceHorizontal_full
    (bs : List (Bool × Bool)) (start : Int × Int) :
    lineFreeEndpoint start.1 (bs.map Prod.fst) =
      (isingDiagonalWalkEndpoint start
        (isingLeapfrogChoiceSteps bs)).1 := by
  induction bs generalizing start with
  | nil =>
      simp [lineFreeEndpoint, isingLeapfrogChoiceSteps,
        isingDiagonalWalkEndpoint, isingDiagonalWalkDisplacement]
  | cons b bs ih =>
      have hih := ih (isingDiagonalWalkNext start
        (isingLeapfrogChoiceStep b))
      rcases b with ⟨bx, byy⟩
      cases bx <;> cases byy <;>
        simp [lineFreeEndpoint, isingLeapfrogChoiceSteps,
          isingLeapfrogChoiceStep, isingDiagonalWalkEndpoint,
          isingDiagonalWalkNext, isingDiagonalWalkDisplacement,
          add_assoc] at hih ⊢ <;> linarith


end
end StatMech.Universality
