/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareDirichletConvergence.Part2
open Finset SimpleGraph Filter Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoxCanonicalPoissonBarrier
    (n : Nat) : (fkSquareBoxPlanar n).V → Real := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  exact isingFiniteGraphPoissonBarrier
    (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
    (fkIsingSquareBox_reachable_boundary n)

noncomputable def fkIsingSquareBoxCanonicalPoissonBarrierBound
    (n : Nat) : Real := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  exact isingFiniteGraphPoissonBarrierBound
    (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
    (fkIsingSquareBox_reachable_boundary n)


end
end StatMech.Universality
