/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDirichletLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareDirichletConvergence.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit
open Filter Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoxPoissonBarrierBound (n : Nat) : Real := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  exact isingFiniteGraphPoissonBarrierBound
    (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
    (fkIsingSquareBox_reachable_boundary n)


end
end StatMech.Universality
