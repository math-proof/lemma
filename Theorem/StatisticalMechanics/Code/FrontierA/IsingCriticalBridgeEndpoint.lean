/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBridgeEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part8
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalBridgeEndpoint
open Filter Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice

noncomputable section

theorem oddPrismCriticalLowerHalfBridgeMeanDensity_eq_spinSquareAverage
    (n : Nat) :
    oddPrismCriticalLowerHalfBridgeMeanDensity n =
      oddPrismCriticalLowerHalfSpinSquareAverage n := by
  letI : DecidableRel (oddPrismLowerHalfGraph n).Adj := Classical.decRel _
  unfold oddPrismCriticalLowerHalfBridgeMeanDensity
    oddPrismCriticalLowerHalfSpinSquareAverage
  rw [replicaBridgeMean_zero]
  congr 1


theorem oddPrismCriticalLowerHalfBridgeMeanDensity_tendsto_zero :
    Tendsto oddPrismCriticalLowerHalfBridgeMeanDensity atTop (nhds 0) := by
  apply oddPrismCriticalLowerHalfSpinSquareAverage_tendsto_zero.congr'
  exact Filter.Eventually.of_forall fun n =>
    (oddPrismCriticalLowerHalfBridgeMeanDensity_eq_spinSquareAverage n).symm


end
end StatMech.FrontierA
