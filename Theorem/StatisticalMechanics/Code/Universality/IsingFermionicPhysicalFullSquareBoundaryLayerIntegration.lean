/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerIntegration


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareFullOrientedRadialIncrementOf_incidence
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareFullOrientedRadialIncrementOf n hn inc
        (.inl (fkIsingSquareInteriorRadialEndpoint n hn e))
        (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e)) = inc e := by
  rw [fkIsingSquareFullOrientedRadialIncrementOf]
  split
  · rw [fkIsingSquareFullIncidenceOfAdjacent_of_incidence n hn e]
  · rename_i h
    exact False.elim
      (h (fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e))

@[simp] theorem fkIsingSquareFullOrientedRadialIncrementOf_incidence_reverse
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real)
    (e : FKIsingSquareInteriorRadialIncidence n hn) :
    fkIsingSquareFullOrientedRadialIncrementOf n hn inc
        (.inr (fkIsingSquareFullFaceOfRadialIncidence n hn e))
        (.inl (fkIsingSquareInteriorRadialEndpoint n hn e)) = -inc e := by
  rw [fkIsingSquareFullOrientedRadialIncrementOf]
  split
  · rw [fkIsingSquareFullIncidenceOfAdjacent_of_incidence n hn e]
  · rename_i h
    exact False.elim
      (h (fkIsingSquareFull_radiallyAdjacent_of_incidence n hn e))

end
end StatMech.Universality
