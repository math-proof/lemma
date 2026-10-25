/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part16


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

namespace FKIsingCaratheodoryApproximation

abbrev BoundaryRadialTensorTentGeometry.VanishingRectangleContourError
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A) :=
  StatMech.Universality.VanishingRectangleContourError
    (BoundaryRadialTensorTentGeometry.interpolant A G)


abbrev BoundaryRadialTensorTentGeometry.ReflectedVanishingRectangleContourError
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A) :=
  StatMech.Universality.VanishingRectangleContourError
    (BoundaryRadialTensorTentGeometry.reflectedInterpolant A G)


end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
