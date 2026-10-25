/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part3


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem faceSouthWest_bondMate (n : Nat) (hn : 0 < n)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareWiredBondMate n hn (faceSouthWestDart n c).1 =
      (faceWestEdge n c, .south) := by
  rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn _
    (faceSouthWestDart n c).2]
  change fkIsingSquareBondMate n hn
    (fkIsingSquareDirectionDart n (faceSWVertex n c) .east
      (faceSW_east_available n c) .counterclockwise) = _
  simp only [fkIsingSquareBondMate,
    fkIsingSquareDirectionDart_endpoint,
    fkIsingSquareDirectionDart_direction,
    fkIsingSquareDirectionDart_turn]
  have hnav : (faceSWVertex n c).1 1 < (n : Int) :=
    faceSW_north_available n c
  have hdir : fkIsingSquareNextDirection n (faceSWVertex n c) .east = .north := by
    simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
      hnav]
  calc
    _ = fkIsingSquareDirectionDart n (faceSWVertex n c) .north
        (faceSW_north_available n c) .clockwise :=
      fkIsingSquareDirectionDart_congr n _ hdir _ _ _
    _ = (faceWestEdge n c, .south) := rfl

end
end StatMech.Universality
