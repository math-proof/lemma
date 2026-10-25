/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointTraceProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectionSampling.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPolynomialEndpointConvergence.Part2


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def isingFermionicQuadraticLipschitzConstant
    (C : NNReal) (k : Nat) : NNReal :=
  C * ⟨(((k + 1 : Nat) : Real) ^ 2), by positivity⟩


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
