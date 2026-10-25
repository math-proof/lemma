/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundary


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

def leftInteriorEastDart
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fkIsingSquareLeftVerticalEdge n hn k, .east), by
    simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
      fkIsingSquareLeftVerticalEdge, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    have hk := k.isLt
    omega⟩

def leftInteriorSouthDart
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    FKIsingSquareInteriorRadialDart n :=
  ⟨(fkIsingSquareLeftVerticalEdge n hn k, .south), by
    simp [fkIsingSquareInteriorFaceKey, fkIsingSquareWedgeFaceKey,
      fkIsingSquareLeftVerticalEdge, fkIsingSquareDartEndpoint,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareLeftVerticalUpper, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite]
    have hk := k.isLt
    omega⟩

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
