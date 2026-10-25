/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Mathlib.Topology.UnitInterval
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part6


namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

def finiteCenteredRadialGridDeeperInterior
    (n : Nat) (mesh : Real) : Set Complex :=
  {z | 1 < (isingCenteredRadialGridCoordinate mesh n z).1 ∧
    (isingCenteredRadialGridCoordinate mesh n z).1 < (2 * n : Nat) - 3 ∧
    1 < (isingCenteredRadialGridCoordinate mesh n z).2 ∧
    (isingCenteredRadialGridCoordinate mesh n z).2 < (2 * n : Nat) - 3}


end
end StatMech.Universality
