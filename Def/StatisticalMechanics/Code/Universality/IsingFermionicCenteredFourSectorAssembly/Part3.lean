/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredFourSectorAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredNESectorRate
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredFourSectorAssembly.Part3


namespace StatMech.Universality

noncomputable section

def FKIsingExpandingCenteredTopDiagonalCellBound
    (L : NNReal) (k I : Nat) : Prop :=
  ∀ (hI0 : 0 < I) (hI : I < 2 * fkIsingExpandingSquareSide k),
    let n := fkIsingExpandingSquareSide k
    let F := fkIsingSquareBoundaryCenteredRadialPatchFullObservable n
      (fkIsingExpandingSquareSide_pos k)
    let normalization := Real.sqrt (2 * fkIsingExpandingSquareMesh k)
    ‖F ⟨I, hI⟩ ⟨2 * n - 2, by omega⟩ / normalization -
        F ⟨I - 1, by omega⟩ ⟨2 * n - 1, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real) ∧
      ‖F ⟨I, hI⟩ ⟨2 * n - 1, by omega⟩ / normalization -
        F ⟨I - 1, by omega⟩ ⟨2 * n - 2, by omega⟩ / normalization‖ ≤
        fkIsingExpandingSquareScale k * (L : Real)


def FKIsingExpandingCenteredRightDiagonalCellBound
    (L : NNReal) (k J : Nat) : Prop :=
  ∀ (hJ0 : 0 < J) (hJ : J < 2 * fkIsingExpandingSquareSide k),
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
