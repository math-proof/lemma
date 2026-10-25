/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part4


namespace StatMech.Universality

open Filter Set Topology Metric

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

noncomputable def fkIsingExpandingSquareRadialSupport (k : Nat) :
    Finset (fkIsingExpandingSquareCaratheodoryApproximation.M k) := by
  classical
  by_cases hk : k = 0
  · exact {.source}
  · let n := fkIsingExpandingSquareSide k
    let m := k + 1
    let R := k / 2
    have hm : m ≤ n := by simp [m, n, fkIsingExpandingSquareSide]; nlinarith
    have hfit : 0 + R + 1 < m := by simp [R, m]; omega
    exact Finset.univ.map
      (fkIsingSquareRadialPatchWindowCarrierEmbedding
        n m 0 0 R hm hfit hfit)

end
end StatMech.Universality
