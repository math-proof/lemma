/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerSwitching.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareFullOrientedRadialIncrementOf
    (n : Nat) (hn : 0 < n)
    (inc : FKIsingSquareInteriorRadialIncidence n hn -> Real) :
    FKIsingSquareFullRadialNode n -> FKIsingSquareFullRadialNode n -> Real := by
  classical
  intro a b
  exact match a, b with
    | .inl x, .inr c =>
        if h : FKIsingSquareFullRadiallyAdjacent n x c then
          inc (fkIsingSquareFullIncidenceOfAdjacent n hn x c h)
        else 0
    | .inr c, .inl x =>
        if h : FKIsingSquareFullRadiallyAdjacent n x c then
          -inc (fkIsingSquareFullIncidenceOfAdjacent n hn x c h)
        else 0
    | _, _ => 0

end
end StatMech.Universality
