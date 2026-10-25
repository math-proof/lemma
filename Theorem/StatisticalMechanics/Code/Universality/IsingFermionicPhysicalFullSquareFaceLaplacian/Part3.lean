/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part2


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem faceWestEdge_eq_south (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    faceWestEdge n c = fkIsingSquareDirectionEdge n (faceNWVertex n c)
      .south (faceNW_south_available n c) := by
  apply Subtype.ext
  change s(faceSWVertex n c,
      fkIsingSquareNeighbor n (faceSWVertex n c) .north
        (faceSW_north_available n c)) =
    s(faceNWVertex n c,
      fkIsingSquareNeighbor n (faceNWVertex n c) .south
        (faceNW_south_available n c))
  rw [Sym2.eq_iff]
  right
  constructor
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSWVertex, faceNWVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSWVertex, faceNWVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]

theorem faceNorthEdge_eq_west (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    faceNorthEdge n c = fkIsingSquareDirectionEdge n (faceNEVertex n c)
      .west (faceNE_west_available n c) := by
  apply Subtype.ext
  change s(faceNWVertex n c,
      fkIsingSquareNeighbor n (faceNWVertex n c) .east
        (faceNW_east_available n c)) =
    s(faceNEVertex n c,
      fkIsingSquareNeighbor n (faceNEVertex n c) .west
        (faceNE_west_available n c))
  rw [Sym2.eq_iff]
  right
  constructor
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceNWVertex, faceNEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceNWVertex, faceNEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]

theorem faceEastEdge_eq_south (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    faceEastEdge n c = fkIsingSquareDirectionEdge n (faceNEVertex n c)
      .south (faceNE_south_available n c) := by
  apply Subtype.ext
  change s(faceSEVertex n c,
      fkIsingSquareNeighbor n (faceSEVertex n c) .north
        (faceSE_north_available n c)) =
    s(faceNEVertex n c,
      fkIsingSquareNeighbor n (faceNEVertex n c) .south
        (faceNE_south_available n c))
  rw [Sym2.eq_iff]
  right
  constructor
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSEVertex, faceNEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSEVertex, faceNEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]

theorem faceSouthEdge_eq_west (n : Nat)
    (c : FKIsingSquareFullFaceNode n) :
    faceSouthEdge n c = fkIsingSquareDirectionEdge n (faceSEVertex n c)
      .west (faceSE_west_available n c) := by
  apply Subtype.ext
  change s(faceSWVertex n c,
      fkIsingSquareNeighbor n (faceSWVertex n c) .east
        (faceSW_east_available n c)) =
    s(faceSEVertex n c,
      fkIsingSquareNeighbor n (faceSEVertex n c) .west
        (faceSE_west_available n c))
  rw [Sym2.eq_iff]
  right
  constructor
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSWVertex, faceSEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]
  · apply Subtype.ext
    funext k
    fin_cases k <;>
      simp [faceSWVertex, faceSEVertex, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite]

end
end StatMech.Universality
