/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFullSquareBoundaryProjectionFixedDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionPolynomial.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFullSquareBoundaryProjectionFixedDomain


namespace StatMech.Universality

open Filter Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def isingFermionicFixedDiamondEndpointLipschitzConstant
    (C : NNReal) (k : Nat) : NNReal :=
  C * ⟨(((k + 2 : Nat) : Real) ^ 4), by positivity⟩

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
