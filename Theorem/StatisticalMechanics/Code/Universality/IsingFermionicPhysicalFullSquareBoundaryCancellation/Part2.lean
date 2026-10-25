/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part2


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquarePerimeterInteriorRadialEndpoint
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) :
    fkIsingSquareInteriorRadialEndpoint n hn
        (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k) =
      fkIsingSquareBoundaryVertex n (side, k) := by
  change fkIsingSquareDartEndpoint n
    (fkIsingSquarePerimeterInteriorRadialDart n side k).1 = _
  cases side <;>
    simp [fkIsingSquarePerimeterInteriorRadialDart,
      fkIsingSquarePerimeterInteriorSide, fkIsingSquarePerimeterEdge,
      fkIsingSquarePerimeterDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation]


theorem fkIsingSquarePerimeterInteriorFace_fixedBoundary_of_free
    (n : Nat) (hn : 0 < n) (side : FKIsingSquareBoundarySide)
    (k : Fin (2 * n)) (hfree : side ≠ .left) :
    fkIsingSquareFullFaceFixedBoundary n
      (fkIsingSquareFullFaceOfRadialIncidence n hn
        (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)) := by
  have hkey := fkIsingSquareFullFaceOfRadialIncidence_key n hn
    (fkIsingSquarePerimeterInteriorRadialIncidence n hn side k)
  change fkIsingSquareInteriorCellKey n _ =
    fkIsingSquareWedgeFaceKey n
      (fkIsingSquarePerimeterInteriorRadialDart n side k).1 at hkey
  unfold fkIsingSquareFullFaceFixedBoundary
  cases side with
  | bottom =>
      left
      have h := congrArg Prod.snd hkey
      simp [fkIsingSquarePerimeterInteriorRadialDart,
        fkIsingSquarePerimeterInteriorSide, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareInteriorCellKey] at h
      omega
  | right =>
      right; left
      have h := congrArg Prod.fst hkey
      simp [fkIsingSquarePerimeterInteriorRadialDart,
        fkIsingSquarePerimeterInteriorSide, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareInteriorCellKey] at h
      omega
  | top =>
      right; right
      have h := congrArg Prod.snd hkey
      simp [fkIsingSquarePerimeterInteriorRadialDart,
        fkIsingSquarePerimeterInteriorSide, fkIsingSquareWedgeFaceKey,
        fkIsingSquarePerimeterEdge, fkIsingSquarePerimeterDirection,
        fkIsingSquareDartEndpoint, fkIsingSquareDartDirection,
        fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_directionEdge,
        fkIsingSquareDirectionEdgeOrientation,
        fkIsingSquareBoundaryVertex, fkIsingSquareBoundarySite,
        fkIsingSquareInteriorCellKey] at h
      omega
  | left => exact False.elim (hfree rfl)


end
end StatMech.Universality
