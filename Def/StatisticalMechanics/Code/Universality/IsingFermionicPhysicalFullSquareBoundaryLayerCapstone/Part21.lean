/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part21


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

def bottomRightCornerCycleCarrier
    (n : Nat) (hn : 0 < n) (z : FKIsingSquareWiredCarrier n) : Prop :=
  z = .dart (bottomRightCornerOtherDart n hn) ∨
  z = .dart (bottomRightCornerCrossDart n hn) ∨
  z = .bond (bottomRightCornerCrossDart n hn) ∨
  z = .bond (fkIsingSquarePerimeterEdge n .right
    (bottomRightCornerZero n hn), .south) ∨
  z = .dart (fkIsingSquarePerimeterEdge n .right
    (bottomRightCornerZero n hn), .south) ∨
  z = .dart (fkIsingSquarePerimeterEdge n .right
    (bottomRightCornerZero n hn), .west) ∨
  z = .bond (fkIsingSquarePerimeterEdge n .right
    (bottomRightCornerZero n hn), .west) ∨
  z = .bond (bottomRightCornerOtherDart n hn)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
