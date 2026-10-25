/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part2


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryLayerInwardSide_eq_interiorSide
    (side : FKIsingSquareBoundarySide) :
    fkIsingSquareBoundaryLayerInwardSide side =
      fkIsingSquarePerimeterInteriorSide side := by
  cases side <;> rfl

@[simp] theorem fkIsingSquareBoundaryLayer_localMate
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerInwardSide side) =
      (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerEndpointSide side) := by
  cases side <;>
    simp [FKIsingMedialDart.localMate,
      fkIsingSquareBoundaryLayerInwardSide,
      fkIsingSquareBoundaryLayerEndpointSide,
      fkIsingSquareClosePerimeter_perimeterEdge]

@[simp] theorem fkIsingSquareBoundaryLayer_complement_localMate
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) :
    FKIsingMedialDart.localMate (fkIsingSquareClosePerimeter n omega)
        (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side) =
      (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquareBoundaryLayerComplementEndpointSide side) := by
  cases side <;>
    simp [FKIsingMedialDart.localMate,
      fkIsingSquareBoundaryLayerComplementInwardSide,
      fkIsingSquareBoundaryLayerComplementEndpointSide,
      fkIsingSquareClosePerimeter_perimeterEdge]


end
end StatMech.Universality
