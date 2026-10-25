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
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionRectangularModel.Part4


namespace StatMech.FrontierA

noncomputable section

theorem rectangularIsingSurfaceTension_nonneg
    {J : Real} (hJ : 0 < J) :
    0 <= rectangularIsingSurfaceTension J :=
  rectangularSurfaceRate_nonneg (fun m n =>
    rectangularDobrushinFreeEnergy_nonneg
      (gaugeCriticalCoupling_pos hJ) m n)


theorem rectangularIsingDobrushin_square_and_iterated_tendsto
    {J : Real} (hJ : 0 < J) :
    Filter.Tendsto
        (fun n : Nat => rectangularSurfaceDensity
          (rectangularIsingDobrushinFreeEnergy J) n n)
        Filter.atTop (nhds (rectangularIsingSurfaceTension J)) /\
      Filter.Tendsto
        (fun k : Nat =>
          ((rectangularIsingDobrushinFreeEnergy_separatelySubadditive hJ).1 k).lim /
            (k : Real))
        Filter.atTop (nhds (rectangularIsingSurfaceTension J)) := by
  exact square_and_iterated_surfaceDensity_tendsto_rate
    (fun m n => rectangularDobrushinFreeEnergy_nonneg
      (gaugeCriticalCoupling_pos hJ) m n)
    (rectangularIsingDobrushinFreeEnergy_separatelySubadditive hJ)
    (rectangularIsingDobrushinFreeEnergy_areaBound hJ)

end
end StatMech.FrontierA
