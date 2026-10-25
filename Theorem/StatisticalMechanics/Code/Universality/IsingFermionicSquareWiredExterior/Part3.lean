/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredExterior.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePrimalConnectivity.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredExterior.Part4
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredArcPathGraph_le_clique (n : Nat) :
    fkIsingSquareWiredArcPathGraph n ≤
      boundaryCliqueGraph (fkIsingSquareWiredArc n) := by
  classical
  intro x y hxy
  rw [boundaryCliqueGraph_adj]
  exact ⟨hxy.1.ne, hxy.2.1, hxy.2.2⟩


end
end StatMech.Universality
