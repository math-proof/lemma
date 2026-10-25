/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionGeometry.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionPolynomial


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

def PhysicalProjectionPolynomialEndpointSafe (k : Nat)
    (e : FKIsingSquareInteriorRadialIncidence
      (isingFermionicProjectionPolynomialSide k)
      (isingFermionicProjectionPolynomialSide_pos k)) : Prop :=
  PhysicalPolynomialEndpointSafe (k + 1) e


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
