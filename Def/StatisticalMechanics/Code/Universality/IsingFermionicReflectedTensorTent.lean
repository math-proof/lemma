/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectedTensorTent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflection.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part4
open Filter Metric Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)

variable (G : BoundaryRadialTensorTentGeometry A)


noncomputable def BoundaryRadialTensorTentGeometry.reflectedInterpolant :
    Nat → Complex → Complex := fun n z ↦
  BoundaryRadialTensorTentGeometry.interpolant A G n
    ((starRingEnd Complex) z)


noncomputable def BoundaryRadialTensorTentGeometry.reflectedTangent :
    ∀ n, A.reflect.M n → Complex :=
  BoundaryRadialTensorTentGeometry.tangent A G

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
