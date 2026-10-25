/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredNESectorRate
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredFourSectorAssembly.Part4


namespace StatMech.Universality

noncomputable section

def FKIsingExpandingCenteredOuterCollarBound
    (L : NNReal) (k : Nat) : Prop :=
  (∀ a b : Nat,
    ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
      (hb : b < 2 * fkIsingExpandingSquareSide k),
    ¬ (a + 2 < 2 * fkIsingExpandingSquareSide k ∧
        b + 1 < 2 * fkIsingExpandingSquareSide k) →
      FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b) ∧
  (∀ a b : Nat,
    ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
      (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
    ¬ (a + 1 < 2 * fkIsingExpandingSquareSide k ∧
        b + 2 < 2 * fkIsingExpandingSquareSide k) →
      FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b)


end
end StatMech.Universality
