/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerIntegration


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareFullHorizontalIncrementOf
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (q : Int × Int) : Real :=
  fkIsingSquareFullOrientedRadialIncrementOf n hn inc
    (fkIsingSquareFullRadialNodeAtCoordinate n q)
    (fkIsingSquareFullRadialNodeAtCoordinate n (q.1 + 1, q.2))

noncomputable def fkIsingSquareFullVerticalIncrementOf
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (q : Int × Int) : Real :=
  fkIsingSquareFullOrientedRadialIncrementOf n hn inc
    (fkIsingSquareFullRadialNodeAtCoordinate n q)
    (fkIsingSquareFullRadialNodeAtCoordinate n (q.1, q.2 + 1))

end
end StatMech.Universality
