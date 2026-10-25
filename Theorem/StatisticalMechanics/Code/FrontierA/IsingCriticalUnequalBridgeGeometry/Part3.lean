/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalUnequalBridgeGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeEndpoint
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Filter Topology

noncomputable section

theorem oddPrismCriticalUnequalBridgeMeanDensity_nonneg
    (n : Nat) (hn : 0 < n) :
    0 <= oddPrismCriticalUnequalBridgeMeanDensity n := by
  unfold oddPrismCriticalUnequalBridgeMeanDensity
  apply div_nonneg
  · rw [oddPrismUnequalBridgeMean_zero_eq_surfaceProductSum
      (Ising.betaC 3) n hn]
    apply Finset.sum_nonneg
    intro q _
    apply mul_nonneg
    · rw [oddPrismLowerBlockSurfaceSpinMean_eq]
      exact oddPrismLowerHalfSurfaceSpinMeanAt_nonneg
        (Ising.betaC 3) isingBetaC_three_pos.le n q.1 q.2
    · exact oddPrismUpperBlockSurfaceSpinMean_nonneg
        (Ising.betaC 3) isingBetaC_three_pos.le n hn q.1 q.2
  · positivity

theorem oddPrismCriticalUnequalBridgeMeanDensity_le_lowerAverage
    (n : Nat) (hn : 0 < n) :
    oddPrismCriticalUnequalBridgeMeanDensity n <=
      oddPrismCriticalLowerHalfSpinAverage n := by
  unfold oddPrismCriticalUnequalBridgeMeanDensity
    oddPrismCriticalLowerHalfSpinAverage
  exact div_le_div_of_nonneg_right
    (oddPrismUnequalBridgeMean_zero_le_surfaceSpinSum
      (Ising.betaC 3) isingBetaC_three_pos.le n hn)
    (sq_nonneg _)


theorem oddPrismCriticalUnequalBridgeMeanDensity_tendsto_zero :
    Tendsto oddPrismCriticalUnequalBridgeMeanDensity atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact oddPrismCriticalUnequalBridgeMeanDensity_nonneg n (by omega)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact oddPrismCriticalUnequalBridgeMeanDensity_le_lowerAverage n (by omega)
  · exact oddPrismCriticalLowerHalfSpinAverage_tendsto_zero


theorem standardCubicInterfaceDensity_critical_le_unequalMeanDensity
    (n : Nat) (hn : 0 < n)
    (hvar : OddPrismUnequalBridgeVarianceOrder (Ising.betaC 3) n) :
    standardCubicInterfaceDensity (Ising.betaC 3) n <=
      2 * Ising.betaC 3 * oddPrismCriticalUnequalBridgeMeanDensity n := by
  rw [standardCubicInterfaceDensity_eq_oddPrismUnequalBridge
    (Ising.betaC 3) n hn]
  unfold oddPrismCriticalUnequalBridgeMeanDensity
  calc
    oddPrismUnequalBridgeFreeEnergy (Ising.betaC 3) n /
        (((2 * n + 1 : Nat) : Real) ^ 2) <=
      (2 * Ising.betaC 3 * unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) (Ising.betaC 3)
        (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
        (fun v => Ising.betaC 3 * oddPrismPlusField n v.1) 0) /
          (((2 * n + 1 : Nat) : Real) ^ 2) :=
      div_le_div_of_nonneg_right
        (oddPrismUnequalBridgeFreeEnergy_le_of_variance_order
          (Ising.betaC 3) isingBetaC_three_pos.le n hvar) (sq_nonneg _)
    _ = 2 * Ising.betaC 3 *
        (unequalReplicaBridgeMean
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) (Ising.betaC 3)
          (fun v => Ising.betaC 3 * oddPrismPlusField n v.1)
          (fun v => Ising.betaC 3 * oddPrismPlusField n v.1) 0 /
            (((2 * n + 1 : Nat) : Real) ^ 2)) := by ring


theorem standardCubicInterfaceDensity_critical_tendsto_zero_of_varianceOrder
    (hvar : forall n, OddPrismUnequalBridgeVarianceOrder
      (Ising.betaC 3) n) :
    Tendsto (standardCubicInterfaceDensity (Ising.betaC 3))
      atTop (nhds 0) := by
  have hu : Tendsto (fun n =>
      2 * Ising.betaC 3 * oddPrismCriticalUnequalBridgeMeanDensity n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      oddPrismCriticalUnequalBridgeMeanDensity_tendsto_zero
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact standardCubicInterfaceDensity_nonneg
      isingBetaC_three_pos.le n (by omega)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact standardCubicInterfaceDensity_critical_le_unequalMeanDensity
      n (by omega) (hvar n)
  · exact hu


theorem rectangularIsingSurfaceTension_critical_eq_zero_of_unequalVarianceOrder
    (hprism : HasPrismCubicalSurfaceComparison (Ising.betaC 3))
    (hvar : forall n, OddPrismUnequalBridgeVarianceOrder
      (Ising.betaC 3) n) :
    rectangularIsingSurfaceTension (Ising.betaC 3) = 0 := by
  apply tendsto_nhds_unique
    (standardCubicInterfaceDensity_tendsto_rectangularIsingSurfaceTension
      isingBetaC_three_pos hprism
      (hasStandardPrismSurfaceComparison (Ising.betaC 3)))
  exact standardCubicInterfaceDensity_critical_tendsto_zero_of_varianceOrder hvar

end
end StatMech.FrontierA
