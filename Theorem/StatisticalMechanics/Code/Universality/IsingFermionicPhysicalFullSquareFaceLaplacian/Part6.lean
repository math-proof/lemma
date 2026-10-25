/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part5


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem faceNorthEast_bondMate (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareWiredBondMate n hn (faceNorthEastDart n c).1 =
      (faceEastEdge n c, .north) := by
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (faceNorthEastDart n c).2]
  rw [show (faceNorthEastDart n c).1 =
      (fkIsingSquareDirectionEdge n (faceNEVertex n c) .west
        (faceNE_west_available n c), .east) by
    apply Prod.ext
    · exact faceNorthEdge_eq_west n c
    · rfl]
  change fkIsingSquareBondMate n hn
    (fkIsingSquareDirectionDart n (faceNEVertex n c) .west
      (faceNE_west_available n c) .counterclockwise) = _
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hsouth : -(n : Int) < (faceNEVertex n c).1 1 :=
    faceNE_south_available n c
  have hdir : fkIsingSquareNextDirection n (faceNEVertex n c) .west = .south := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable, hsouth]
  calc
    _ = fkIsingSquareDirectionDart n (faceNEVertex n c) .south
        (faceNE_south_available n c) .clockwise :=
      fkIsingSquareDirectionDart_congr n _ hdir _ _ _
    _ = (fkIsingSquareDirectionEdge n (faceNEVertex n c) .south
          (faceNE_south_available n c), .north) := rfl
    _ = (faceEastEdge n c, .north) := by rw [faceEastEdge_eq_south]

end
end StatMech.Universality
