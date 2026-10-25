/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part4


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

noncomputable def fkIsingSquareBoundaryLayerComplementVertexFermion
    (n : Nat) (hn : 0 < n)
    (side : FKIsingSquareBoundarySide) (k : Fin (2 * n)) : Complex :=
  let D := fkIsingSquareBoundaryRestrictedDobrushinDomain n hn
  (isingFermionicBoundaryVertexNormalization : Complex) *
    (D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementInwardSide side)) +
      D.fermionicObservable
        (.dart (fkIsingSquarePerimeterEdge n side k,
          fkIsingSquareBoundaryLayerComplementEndpointSide side)))

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
