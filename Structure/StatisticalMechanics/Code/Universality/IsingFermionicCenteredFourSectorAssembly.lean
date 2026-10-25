/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredNESectorRate
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCenteredFourSectorAssembly.Part4


namespace StatMech.Universality

noncomputable section

structure FKIsingExpandingCenteredTopRightBoundaryEdgeBounds
    (L : NNReal) (k : Nat) : Prop where
  horizontalRight : ∀ a b : Nat,
    ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
      (hb : b < 2 * fkIsingExpandingSquareSide k),
      a + 2 = 2 * fkIsingExpandingSquareSide k →
        FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b
  horizontalTop : ∀ a b : Nat,
    ∀ (ha : a + 1 < 2 * fkIsingExpandingSquareSide k)
      (hb : b < 2 * fkIsingExpandingSquareSide k),
      b + 1 = 2 * fkIsingExpandingSquareSide k →
        FKIsingExpandingCenteredHorizontalNeighborBound (2 * L) k a b
  verticalRight : ∀ a b : Nat,
    ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
      (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      a + 1 = 2 * fkIsingExpandingSquareSide k →
        FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b
  verticalTop : ∀ a b : Nat,
    ∀ (ha : a < 2 * fkIsingExpandingSquareSide k)
      (hb : b + 1 < 2 * fkIsingExpandingSquareSide k),
      b + 2 = 2 * fkIsingExpandingSquareSide k →
        FKIsingExpandingCenteredVerticalNeighborBound (2 * L) k a b


end
end StatMech.Universality
