/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part8


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

theorem fkIsingSquareBottomBoundaryMissingSouthObservable_projection_east
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
    isingProj Complex.I
        (fkIsingSquareBottomBoundaryMissingSouthObservable n hn k) =
      isingProj Complex.I
        (fkIsingSquareBottomBoundaryMedialObservable n hn k1) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let east := isingProj Complex.I
    (fkIsingSquareBottomBoundaryMedialObservable n hn k1)
  let west := isingProj (-1)
    (fkIsingSquareBottomBoundaryMedialObservable n hn k0)
  change isingProj Complex.I
      (bottomMissingSouthProjectionReconstruction east west) = east
  exact bottomMissingSouthProjectionReconstruction_projection_east
    east west (isingProj_I_conj_line _) (isingProj_negOne_conj_line _)

theorem fkIsingSquareBottomBoundaryMissingSouthObservable_projection_west
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n - 1)) :
    let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
    isingProj (-1)
        (fkIsingSquareBottomBoundaryMissingSouthObservable n hn k) =
      isingProj (-1)
        (fkIsingSquareBottomBoundaryMedialObservable n hn k0) := by
  let k0 : Fin (2 * n) := ⟨k.1, by omega⟩
  let k1 : Fin (2 * n) := ⟨k.1 + 1, by omega⟩
  let east := isingProj Complex.I
    (fkIsingSquareBottomBoundaryMedialObservable n hn k1)
  let west := isingProj (-1)
    (fkIsingSquareBottomBoundaryMedialObservable n hn k0)
  change isingProj (-1)
      (bottomMissingSouthProjectionReconstruction east west) = west
  exact bottomMissingSouthProjectionReconstruction_projection_west
    east west (isingProj_I_conj_line _) (isingProj_negOne_conj_line _)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
