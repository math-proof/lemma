module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
public import Mathlib.Topology.UnitInterval
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

noncomputable def isingCenteredRadialGridCoordinate
    (mesh : Real) (n : Nat) (z : Complex) : Real × Real :=
  isingRadialGridCoordinate mesh (z + (mesh * n : Real))

end
end StatMech.Universality
