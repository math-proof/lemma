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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem tendsto_isingFermionicQuadraticLipschitz_mul_polynomialMesh
    (C : NNReal) :
    Tendsto (fun k =>
      (isingFermionicQuadraticLipschitzConstant C k : Real) *
        isingFermionicPolynomialMesh k) atTop (nhds 0) := by
  let u : Nat -> Real := fun k => 1 / ((k : Real) + 1)
  have hu : Tendsto u atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hCu : Tendsto (fun k => (C : Real) * u k) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hu
  convert hCu using 1
  funext k
  unfold isingFermionicQuadraticLipschitzConstant
    isingFermionicPolynomialMesh u
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  push_cast
  field_simp [hk.ne']
  rfl


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
