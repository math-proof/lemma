/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerCapstone.Part11


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

open FKIsingSquareBoundaryLayerVertexIntegratedPrimitive

open FKIsingSquareBoundaryLayerIntegratedPrimitive

noncomputable def isingPrimalProjectionDivergenceWithoutEast
    (north south west : Complex) : Real :=
  Complex.normSq (isingProj (-Complex.I) north) -
      Complex.normSq (isingProj (-1) north) +
    Complex.normSq (isingProj Complex.I south) -
      Complex.normSq (isingProj 1 south) +
    Complex.normSq (isingProj (-1) west) -
      Complex.normSq (isingProj Complex.I west)


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
