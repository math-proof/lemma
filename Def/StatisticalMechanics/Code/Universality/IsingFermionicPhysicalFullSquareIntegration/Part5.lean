/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareFullOriginVertex (n : Nat) :
    FKIsingSquareFullVertexNode n := by
  refine ⟨![0, 0], ?_⟩
  intro k
  fin_cases k <;> simp


noncomputable def fkIsingSquareFullRadialNodeAtCoordinate
    (n : Nat) (q : Int × Int) : FKIsingSquareFullRadialNode n := by
  classical
  exact if hq : FKIsingSquareFullDiamond n q then
      fkIsingSquareFullRadialNodeOfCoordinate n q hq
    else .inl (fkIsingSquareFullOriginVertex n)

end
end StatMech.Universality
