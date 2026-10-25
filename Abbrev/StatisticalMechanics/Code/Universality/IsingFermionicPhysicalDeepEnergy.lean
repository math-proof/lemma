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


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

abbrev FKIsingSquareRadialPatchInteriorCell (m : Nat) :=
  Fin (m - 1) × Fin (m - 1)

end
end StatMech.Universality
