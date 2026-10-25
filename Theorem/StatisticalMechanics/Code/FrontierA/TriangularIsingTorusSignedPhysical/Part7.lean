/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical.Part7
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem triangularKacWardPhaseRoot_pow_four :
    triangularKacWardPhaseRoot ^ 4 = Complex.I :=
  Classical.choose_spec
    (IsAlgClosed.exists_pow_nat_eq Complex.I (by norm_num : 0 < 4))


theorem triangularTorusIsingPartition_freeEnergy_tendsto_ray
    (beta J : Real) (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun n : Nat =>
        -Real.log (triangularTorusIsingPartitionSequence
          beta beta (beta * J) n) / (n + 3 : Real) ^ 2)
      Filter.atTop
      (nhds (triangularIsingFreeEnergyValue beta beta (beta * J))) := by
  by_cases hJ : -1 < J
  · exact triangularTorusIsingPartition_freeEnergy_tendsto_gt_neg_one
      triangularKacWardPhaseRoot triangularKacWardPhaseRoot_pow_four hbeta hJ
  · exact triangularTorusIsingPartition_freeEnergy_tendsto_le_neg_one
      triangularKacWardPhaseRoot triangularKacWardPhaseRoot_pow_four hbeta
        (le_of_not_gt hJ)

end StatMech.FrontierA
