/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectedTensorTent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflection.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent
open Filter Metric Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)

variable (G : BoundaryRadialTensorTentGeometry A)


noncomputable def BoundaryRadialTensorTentGeometry.toReflectedStableFullMedialInterpolation
    (H : A.MeshUniformCompactHolder
      (BoundaryRadialTensorTentGeometry.interpolant A G)) :
    A.reflect.StableFullMedialInterpolation (G.reflectedTangent A) :=
  StableFullMedialInterpolation.ofTensorTentCompactHolder A.reflect
    (G.reflectedTangent A) (G.reflectedInterpolant A)
    (G.reflectedInterpolant_continuous A)
    (G.reflected_projectedMedial A)
    H.reflected


end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
