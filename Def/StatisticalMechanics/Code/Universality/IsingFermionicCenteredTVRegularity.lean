/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredStoppedWalk.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredFourSectorAssembly.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTVRegularity


namespace StatMech.Universality

open Metric Set

noncomputable section

def finiteCenteredRadialGridMarginInterior
    (n rho : Nat) (mesh : Real) : Set Complex :=
  {z | (rho : Real) + 2 <
      (isingCenteredRadialGridCoordinate mesh n z).1 ∧
    (isingCenteredRadialGridCoordinate mesh n z).1 + rho + 5 < 2 * n ∧
    (rho : Real) + 2 <
      (isingCenteredRadialGridCoordinate mesh n z).2 ∧
    (isingCenteredRadialGridCoordinate mesh n z).2 + rho + 5 < 2 * n}


end
end StatMech.Universality
