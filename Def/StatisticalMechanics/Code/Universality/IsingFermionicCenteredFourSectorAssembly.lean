/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredNESectorRate
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredFourSectorAssembly


namespace StatMech.Universality

noncomputable section

def FKIsingExpandingCenteredDiagonalCellBound
    (L : NNReal) (k i j : Nat) : Prop :=
  ∀ (hi0 : 0 < i)
    (hi1 : i + 1 < 2 * fkIsingExpandingSquareSide k)
    (hj0 : 0 < j)
    (hj1 : j + 1 < 2 * fkIsingExpandingSquareSide k),
    let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
    ‖F ⟨i, by omega⟩ ⟨j - 1, by omega⟩ / normalization -
        F ⟨i - 1, by omega⟩ ⟨j, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real) ∧
      ‖F ⟨i, by omega⟩ ⟨j, by omega⟩ / normalization -
        F ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real)


def FKIsingExpandingCenteredRightEvenDiagonalCellBound
    (L : NNReal) (k J : Nat) : Prop :=
  ∀ (hJ0 : 0 < J)
    (hJ : J < 2 * fkIsingExpandingSquareSide k)
    (heven : Even ((2 * fkIsingExpandingSquareSide k - 1) + J)),
    let n := fkIsingExpandingSquareSide k
    let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
      (fkIsingExpandingSquareSide_pos k)
    let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
    ‖F ⟨2 * n - 1, by omega⟩ ⟨J - 1, by omega⟩ / normalization -
        F ⟨2 * n - 2, by omega⟩ ⟨J, hJ⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real) ∧
      ‖F ⟨2 * n - 1, by omega⟩ ⟨J, hJ⟩ / normalization -
        F ⟨2 * n - 2, by omega⟩ ⟨J - 1, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real)


end
end StatMech.Universality
