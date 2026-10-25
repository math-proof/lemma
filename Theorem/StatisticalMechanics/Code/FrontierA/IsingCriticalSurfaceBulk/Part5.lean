/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part4
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

theorem oddPrismLowerHalfSurfaceSpinMeanAt_nonneg
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (i j : Fin (2 * n + 1)) :
    0 <= oddPrismLowerHalfSurfaceSpinMeanAt beta n i j := by
  letI : DecidableRel (oddPrismInternalGraph n).Adj := Classical.decRel _
  dsimp only [oddPrismLowerHalfSurfaceSpinMeanAt]
  rw [<- spinProd_singleton]
  apply ghsvp_expJ_nonneg
  · exact fun _ _ => hbeta
  · intro v
    exact mul_nonneg hbeta (Nat.cast_nonneg _)


theorem oddPrismCriticalLowerHalfSpinSquareAverage_le_plus
    (n : Nat) :
    oddPrismCriticalLowerHalfSpinSquareAverage n <=
      oddPrismCriticalSurfaceSpinSquareAverage n := by
  unfold oddPrismCriticalLowerHalfSpinSquareAverage
    oddPrismCriticalSurfaceSpinSquareAverage
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro q _
  have hlow0 := oddPrismLowerHalfSurfaceSpinMeanAt_nonneg
    (Ising.betaC 3) isingBetaC_three_pos.le n q.1 q.2
  have hplus0 := oddPrismPlusSpinMean_nonneg
    (Ising.betaC 3) isingBetaC_three_pos.le n
      (oddPrismLowerHalfSurfaceSite n q.1 q.2).1
  have hle := oddPrismLowerHalfSurfaceSpinMeanAt_le_plus
    (Ising.betaC 3) isingBetaC_three_pos.le n q.1 q.2
  exact (sq_le_sq₀ hlow0 hplus0).2 hle

theorem oddPrismCriticalLowerHalfSpinSquareAverage_nonneg (n : Nat) :
    0 <= oddPrismCriticalLowerHalfSpinSquareAverage n := by
  unfold oddPrismCriticalLowerHalfSpinSquareAverage
  positivity


theorem oddPrismCriticalLowerHalfSpinSquareAverage_tendsto_zero :
    Tendsto oddPrismCriticalLowerHalfSpinSquareAverage atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall
      oddPrismCriticalLowerHalfSpinSquareAverage_nonneg
  · exact Filter.Eventually.of_forall
      oddPrismCriticalLowerHalfSpinSquareAverage_le_plus
  · exact oddPrismCriticalSurfaceSpinSquareAverage_tendsto_zero


end
end StatMech.FrontierA
