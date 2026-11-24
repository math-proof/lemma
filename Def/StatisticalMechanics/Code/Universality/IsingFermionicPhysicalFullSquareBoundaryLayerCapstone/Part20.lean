module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part20


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

def bottomRightCornerOtherDart (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  (fkIsingSquarePerimeterEdge n .bottom (bottomRightCornerLast n hn), .north)

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
