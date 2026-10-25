/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDeepEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactVariation.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointPointwise
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareRadialPatchInteriorCell_succ_lt
    {m : Nat} (i : Fin (m - 1)) : i.1 + 1 < m := by
  omega

end
end StatMech.Universality
