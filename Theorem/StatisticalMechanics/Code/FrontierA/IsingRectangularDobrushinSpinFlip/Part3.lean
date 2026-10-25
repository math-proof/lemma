/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
import Def.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part3
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

theorem rectangularPrismTwistedPartition_eq_dobrushinPartition
    (J beta : Real) (m n h : Nat) :
    rectangularPrismTwistedPartition J beta m n h =
      rectangularPrismDobrushinPartition J beta m n h := by
  rw [rectangularPrismTwistedPartition_eq_monomialInteractionPartition]
  unfold monomialInteractionPartition rectangularPrismDobrushinPartition
  rw [← (rectangularPrismUpperHalfFlipEquiv m n h).sum_comp]
  apply Finset.sum_congr rfl
  intro sigma _
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  exact reverseSheet_mul_monomial_upperHalfFlip J beta q sigma


theorem rectangularDobrushinFreeEnergy_eq_boundaryRatio
    (J beta : Real) (m n h : Nat) :
    rectangularDobrushinFreeEnergy J beta m n h =
      Real.log (rectangularPrismPlusPartition J beta m n h) -
        Real.log (rectangularPrismDobrushinPartition J beta m n h) := by
  rw [rectangularDobrushinFreeEnergy,
    rectangularPrismTwistedPartition_eq_dobrushinPartition]

end
end StatMech.Ising
