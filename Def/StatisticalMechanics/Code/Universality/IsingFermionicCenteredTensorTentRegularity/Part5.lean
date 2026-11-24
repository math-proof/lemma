module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
public import Mathlib.Topology.UnitInterval
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part5


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

def finiteCenteredRadialGridStrictInterior
    (n : Nat) (mesh : Real) : Set Complex :=
  {z | 1 < (isingCenteredRadialGridCoordinate mesh n z).1 ∧
    (isingCenteredRadialGridCoordinate mesh n z).1 < (2 * n : Nat) - 2 ∧
    1 < (isingCenteredRadialGridCoordinate mesh n z).2 ∧
    (isingCenteredRadialGridCoordinate mesh n z).2 < (2 * n : Nat) - 2}


end
end StatMech.Universality
