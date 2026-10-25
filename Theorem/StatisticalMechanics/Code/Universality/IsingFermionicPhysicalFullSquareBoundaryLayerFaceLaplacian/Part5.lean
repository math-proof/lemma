/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part4


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem faceWestEast_bondMate (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareWiredBondMate n hn (faceWestEastDart n c).1 =
      (faceNorthEdge n c, .south) := by
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (faceWestEastDart n c).2]
  rw [show (faceWestEastDart n c).1 =
      (fkIsingSquareDirectionEdge n (faceNWVertex n c) .south
        (faceNW_south_available n c), .east) by
    apply Prod.ext
    · exact faceWestEdge_eq_south n c
    · rfl]
  change fkIsingSquareBondMate n hn
    (fkIsingSquareDirectionDart n (faceNWVertex n c) .south
      (faceNW_south_available n c) .counterclockwise) = _
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have heast : (faceNWVertex n c).1 0 < (n : Int) :=
    faceNW_east_available n c
  have hdir : fkIsingSquareNextDirection n (faceNWVertex n c) .south = .east := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable, heast]
  calc
    _ = fkIsingSquareDirectionDart n (faceNWVertex n c) .east
        (faceNW_east_available n c) .clockwise :=
      fkIsingSquareDirectionDart_congr n _ hdir _ _ _
    _ = (faceNorthEdge n c, .south) := rfl

end
end StatMech.Universality
