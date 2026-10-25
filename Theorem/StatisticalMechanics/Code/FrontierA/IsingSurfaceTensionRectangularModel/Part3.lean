/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFeketeIdentification
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCriticalCoupling
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionRectangularModel.Part3


namespace StatMech.FrontierA

noncomputable section

theorem rectangularIsingDobrushinFreeEnergy_eq_disorder
    {J : Real} (hJ : 0 < J) {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    rectangularIsingDobrushinFreeEnergy J m n =
      finiteRectangularIsingDisorderFreeEnergy J m n := by
  rw [rectangularIsingDobrushinFreeEnergy,
    rectangularDobrushinFreeEnergy_eq_dualIsingDisorder
      (gaugeCriticalCoupling_pos hJ) hm hn]
  unfold cubicalRectangularDisorderFreeEnergy
  unfold finiteRectangularIsingDisorderFreeEnergy
  rw [gaugeDualCoupling_gaugeCriticalCoupling hJ]

theorem rectangularIsingDobrushinFreeEnergy_separatelySubadditive
    {J : Real} (hJ : 0 < J) :
    SeparatelySubadditive (rectangularIsingDobrushinFreeEnergy J) := by
  simpa [rectangularIsingDobrushinFreeEnergy] using
    rectangularDobrushinFreeEnergy_separatelySubadditive
      (gaugeCriticalCoupling_pos hJ)

theorem rectangularIsingDobrushinFreeEnergy_areaBound
    {J : Real} (hJ : 0 < J) :
    HasRectangularAreaBound (rectangularIsingDobrushinFreeEnergy J) := by
  simpa [rectangularIsingDobrushinFreeEnergy] using
    rectangularDobrushinFreeEnergy_areaBound (gaugeCriticalCoupling_pos hJ)


end
end StatMech.FrontierA
