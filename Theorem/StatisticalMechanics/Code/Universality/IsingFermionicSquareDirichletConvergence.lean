/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareDirichletConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDirichletComparison.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareDirichletConvergence
open Finset SimpleGraph Filter Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareMarkedA_mem_boxBoundary (n : Nat) :
    fkIsingSquareBoxBoundary n (fkIsingSquareMarkedA n) := by
  refine ⟨0, ?_⟩
  simp [fkIsingSquareBoxBoundary, fkIsingSquareMarkedA]


theorem fkIsingSquareBox_reachable_boundary (n : Nat) :
    ∀ x : (fkSquareBoxPlanar n).V, ∃ b,
      fkIsingSquareBoxBoundary n b ∧
        (fkSquareBoxPlanar n).G.Reachable x b := by
  intro x
  refine ⟨fkIsingSquareMarkedA n,
    fkIsingSquareMarkedA_mem_boxBoundary n, ?_⟩
  exact StatMech.FrontierB.boxGraph_preconnected 2 n x
    (fkIsingSquareMarkedA n)


end
end StatMech.Universality
