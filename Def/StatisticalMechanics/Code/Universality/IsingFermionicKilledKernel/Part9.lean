/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part8


namespace StatMech.Universality

open Finset

noncomputable section

def IsingLeapfrogDiffusiveExitInputs (A B : Real) : Prop :=
  0 ≤ A ∧ 0 ≤ B ∧
    ∀ (R ρ : Nat) (p p' : IsingLeapfrogBox R),
      0 < ρ →
      IsingLeapfrogInteriorMargin R ρ p →
      IsingLeapfrogInteriorMargin R ρ p' →
      IsingLeapfrogDiagonalAdjacent p p' →
      (∀ q, |isingLeapfrogExitKernel R (ρ * ρ) p q -
          isingLeapfrogExitKernel R (ρ * ρ + 1) p' q| ≤
        A / (ρ : Real) ^ 2) ∧
      (∑ q, |isingLeapfrogStoppedKernel R (ρ * ρ) p q -
          isingLeapfrogStoppedKernel R (ρ * ρ + 1) p' q|) ≤
        B / (ρ : Real)

end
end StatMech.Universality
