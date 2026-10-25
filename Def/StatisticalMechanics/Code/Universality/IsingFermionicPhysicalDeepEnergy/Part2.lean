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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareRadialPatchDeepCells
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m) (r : Nat) :
    Finset (FKIsingSquareRadialPatchInteriorCell m) := by
  classical
  exact Finset.univ.filter fun c ↦
    fkIsingSquareRadialPatchCellPrimalDart n m hm c ∈
        fkIsingSquareRadialPatchPrimalDeepDarts n m hm (by omega) r ∧
      fkIsingSquareRadialPatchCellDualDart m c ∈
        fkIsingSquareRadialPatchDualDeepDarts m hm2 r


end
end StatMech.Universality
