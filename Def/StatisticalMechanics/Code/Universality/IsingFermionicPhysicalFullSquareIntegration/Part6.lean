/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareFullHorizontalIncrement
    (n : Nat) (hn : 0 < n) (q : Int × Int) : Real :=
  fkIsingSquareFullOrientedRadialIncrement n hn
    (fkIsingSquareFullRadialNodeAtCoordinate n q)
    (fkIsingSquareFullRadialNodeAtCoordinate n (q.1 + 1, q.2))

noncomputable def fkIsingSquareFullVerticalIncrement
    (n : Nat) (hn : 0 < n) (q : Int × Int) : Real :=
  fkIsingSquareFullOrientedRadialIncrement n hn
    (fkIsingSquareFullRadialNodeAtCoordinate n q)
    (fkIsingSquareFullRadialNodeAtCoordinate n (q.1, q.2 + 1))

end
end StatMech.Universality
