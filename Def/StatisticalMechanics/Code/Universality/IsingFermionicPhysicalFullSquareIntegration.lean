/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def FKIsingSquareFullDiamond (n : Nat) (q : Int × Int) : Prop :=
  -(2 * (n : Int)) ≤ q.1 + q.2 ∧ q.1 + q.2 ≤ 2 * (n : Int) ∧
    -(2 * (n : Int)) ≤ q.1 - q.2 ∧ q.1 - q.2 ≤ 2 * (n : Int)

end
end StatMech.Universality
