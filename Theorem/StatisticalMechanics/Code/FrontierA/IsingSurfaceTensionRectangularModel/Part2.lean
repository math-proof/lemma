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
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionRectangularModel.Part2


namespace StatMech.FrontierA

noncomputable section

theorem rectangularDobrushinSurfaceRate_nonneg
    {beta : Real} (hbeta : 0 < beta) :
    0 <= rectangularDobrushinSurfaceRate beta :=
  rectangularSurfaceRate_nonneg
    (fun m n => rectangularDobrushinFreeEnergy_nonneg hbeta m n)


theorem rectangularDobrushin_square_and_iterated_tendsto
    {beta : Real} (hbeta : 0 < beta) :
    Filter.Tendsto
        (fun n : Nat => rectangularSurfaceDensity
          (rectangularDobrushinFreeEnergy beta) n n)
        Filter.atTop (nhds (rectangularDobrushinSurfaceRate beta)) /\
      Filter.Tendsto
        (fun k : Nat =>
          ((rectangularDobrushinFreeEnergy_separatelySubadditive hbeta).1 k).lim /
            (k : Real))
        Filter.atTop (nhds (rectangularDobrushinSurfaceRate beta)) := by
  exact square_and_iterated_surfaceDensity_tendsto_rate
    (fun m n => rectangularDobrushinFreeEnergy_nonneg hbeta m n)
    (rectangularDobrushinFreeEnergy_separatelySubadditive hbeta)
    (rectangularDobrushinFreeEnergy_areaBound hbeta)


end
end StatMech.FrontierA
