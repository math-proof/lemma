/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFourthMoment
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLineChoiceRun_append_endpointRace
    (n : Nat) (p : IsingLineBox n) (a b : List Bool) :
    isingLineChoiceRun n p (a ++ b) =
      isingLineChoiceRun n (isingLineChoiceRun n p a) b := by
  induction a generalizing p with
  | nil => rfl
  | cons x a ih =>
      simp only [List.cons_append, isingLineChoiceRun]
      exact ih (isingLineChoiceNext n p x)

theorem isingLineChoiceRun_of_boundary_endpointRace
    (n : Nat) (p : IsingLineBox n) (hp : isingLineBoxBoundary n p)
    (bs : List Bool) : isingLineChoiceRun n p bs = p := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [isingLineChoiceRun]
      rw [show isingLineChoiceNext n p b = p by
        simp [isingLineChoiceNext, hp]]
      exact ih

end
end StatMech.Universality
