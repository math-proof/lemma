/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryCompactAverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalBoundaryAverage
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryCompactAverage


namespace StatMech.Universality

open Filter Set Topology Metric

noncomputable section

noncomputable def fkIsingExpandingBoundarySquareRadialSupport (k : Nat) :
    Finset (fkIsingExpandingBoundarySquareCaratheodoryApproximation.M k) := by
  classical
  by_cases hk : 15 ≤ k
  · let n := fkIsingExpandingSquareSide k
    let m := k + 1
    let base := k / 4
    let R := k / 4
    have hm : m ≤ n := by
      simp [m, n, fkIsingExpandingSquareSide]
      nlinarith
    have hfit : base + R + 1 < m := by
      simp [base, R, m]
      omega
    exact Finset.univ.map
      (fkIsingSquareRadialPatchWindowCarrierEmbedding
        n m base base R hm hfit hfit)
  · exact {.source}

end
end StatMech.Universality
