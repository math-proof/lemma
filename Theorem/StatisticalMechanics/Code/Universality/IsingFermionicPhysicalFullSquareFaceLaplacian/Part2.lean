/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem faceSW_east_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceSWVertex n c) .east := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change (fkIsingSquareInteriorCellKey n c).1 < (n : Int)
  exact hp.2.1

theorem faceSW_north_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceSWVertex n c) .north := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change (fkIsingSquareInteriorCellKey n c).2 < (n : Int)
  exact hp.2.2.2

theorem faceSE_north_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceSEVertex n c) .north := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change (fkIsingSquareInteriorCellKey n c).2 < (n : Int)
  exact hp.2.2.2

theorem faceNW_east_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceNWVertex n c) .east := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change (fkIsingSquareInteriorCellKey n c).1 < (n : Int)
  exact hp.2.1

theorem faceNW_south_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceNWVertex n c) .south := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  simp [fkIsingSquareInteriorFaceKey] at hp
  change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2 + 1
  omega

theorem faceNE_west_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceNEVertex n c) .west := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  simp [fkIsingSquareInteriorFaceKey] at hp
  change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1 + 1
  omega

theorem faceNE_south_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceNEVertex n c) .south := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  simp [fkIsingSquareInteriorFaceKey] at hp
  change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2 + 1
  omega

theorem faceSE_west_available (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    fkIsingSquareDirectionAvailable n (faceSEVertex n c) .west := by
  have hp := fkIsingSquareInteriorCellKey_interior n c
  simp [fkIsingSquareInteriorFaceKey] at hp
  change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1 + 1
  omega

end
end StatMech.Universality
