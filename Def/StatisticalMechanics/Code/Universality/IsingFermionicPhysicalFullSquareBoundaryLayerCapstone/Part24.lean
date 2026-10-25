/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part24


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

def topRightCornerCycleCarrier
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) : Prop :=
  z = .dart (topRightCornerOtherDart n hn) ∨
  z = .dart (topRightCornerCrossDart n hn) ∨
  z = .bond (topRightCornerCrossDart n hn) ∨
  z = .bond (fkIsingSquarePerimeterEdge n .top
    (bottomRightCornerZero n hn), .east) ∨
  z = .dart (fkIsingSquarePerimeterEdge n .top
    (bottomRightCornerZero n hn), .east) ∨
  z = .dart (fkIsingSquarePerimeterEdge n .top
    (bottomRightCornerZero n hn), .north) ∨
  z = .bond (fkIsingSquarePerimeterEdge n .top
    (bottomRightCornerZero n hn), .north) ∨
  z = .bond (topRightCornerOtherDart n hn)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
