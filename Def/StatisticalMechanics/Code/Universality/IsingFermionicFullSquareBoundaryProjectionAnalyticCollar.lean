/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionAnalyticCollar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionFixedDomain.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStripCauchyFirstOrder


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def isingFermionicFixedDiamondEndpointCollar (k : Nat) : Real :=
  (1 / ((k : Real) + 2)) ^ 4

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
