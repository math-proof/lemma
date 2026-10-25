/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareFullRadialNodeOfCoordinate_coordinate
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    fkIsingSquareFullRadialNodeCoordinate n
      (fkIsingSquareFullRadialNodeOfCoordinate n q hq) = q :=
  Classical.choose_spec (fkIsingSquareFull_exists_node_of_mem_diamond n q hq)

@[simp] theorem fkIsingSquareFullRadialNodeOfCoordinate_inverse
    (n : Nat) (z : FKIsingSquareFullRadialNode n) :
    fkIsingSquareFullRadialNodeOfCoordinate n
        (fkIsingSquareFullRadialNodeCoordinate n z)
        (fkIsingSquareFullRadialNodeCoordinate_mem_diamond n z) = z := by
  apply fkIsingSquareFullRadialNodeCoordinate_injective n
  exact fkIsingSquareFullRadialNodeOfCoordinate_coordinate n _ _

end
end StatMech.Universality
