/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalBoundaryInfluence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalReduction
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityVaryingTemperature.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingMinusTIFromPlacement
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part2
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Lattice StatMech.ConfigSpace StatMech.FK
  StatMech.Sharpness

noncomputable section

variable {d : Nat}


theorem oddPrismLowerHalfSurfaceSpinMeanAt_le_plus
    (beta : Real) (hbeta : 0 <= beta) (n : Nat)
    (i j : Fin (2 * n + 1)) :
    oddPrismLowerHalfSurfaceSpinMeanAt beta n i j <=
      oddPrismPlusSpinMean beta n (oddPrismLowerHalfSurfaceSite n i j).1 := by
  letI : DecidableRel (oddPrismInternalGraph n).Adj := Classical.decRel _
  let P : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Prop :=
    fun v => v.z.val <= n
  have hfield : forall v, 0 <= beta * oddPrismPlusField n v := by
    intro v
    exact mul_nonneg hbeta (Nat.cast_nonneg _)
  have h := expJ_spin_induce_le_inhomogeneous (oddPrismInternalGraph n) P
    beta hbeta (fun v => beta * oddPrismPlusField n v) hfield
    (oddPrismLowerHalfSurfaceSite n i j)
  simpa [oddPrismLowerHalfSurfaceSpinMeanAt, oddPrismPlusSpinMean, P,
    oddPrismInternalGraph_edgeFinset] using h


theorem oddPrismLowerHalfSurfaceSpinMean_le_plus
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) :
    oddPrismLowerHalfSurfaceSpinMean beta n <=
      oddPrismPlusSpinMean beta n (oddPrismLowerHalfCenter n).1 := by
  letI : DecidableRel (oddPrismInternalGraph n).Adj := Classical.decRel _
  let P : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Prop :=
    fun v => v.z.val <= n
  have hfield : forall v,
      0 <= beta * oddPrismPlusField n v := by
    intro v
    exact mul_nonneg hbeta (Nat.cast_nonneg _)
  have h := expJ_spin_induce_le_inhomogeneous (oddPrismInternalGraph n) P
    beta hbeta
    (fun v => beta * oddPrismPlusField n v) hfield
    (oddPrismLowerHalfCenter n)
  simpa [oddPrismLowerHalfSurfaceSpinMean, oddPrismPlusSpinMean, P,
    oddPrismInternalGraph_edgeFinset] using h

@[simp] theorem oddPrismLowerHalfCenter_to_origin (n : Nat) :
    (rectangularPrismSiteEquivSctBoxDobrushin n
      (oddPrismLowerHalfCenter n).1).1 = origin 3 := by
  funext i
  fin_cases i <;> simp [oddPrismLowerHalfCenter, origin]


theorem isingCritical_oddPrismPlusCenter_tendsto_zero :
    Tendsto (fun n => oddPrismPlusSpinMean (Ising.betaC 3) n
        (oddPrismLowerHalfCenter n).1) atTop (nhds 0) := by
  have h := plusMeasure_spin_full_tendsto_magnetization
    (d := 3) (Ising.betaC 3) isingBetaC_three_pos.le (origin 3)
  rw [magnetization_three_isingBetaC_eq_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => by
    dsimp only
    simpa using (oddPrismPlusSpinMean_eq_plusMeasure_integral
      (Ising.betaC 3) n (oddPrismLowerHalfCenter n).1).symm

theorem oddPrismLowerHalfSurfaceSpinMean_nonneg
    (beta : Real) (hbeta : 0 <= beta) (n : Nat) :
    0 <= oddPrismLowerHalfSurfaceSpinMean beta n := by
  dsimp only [oddPrismLowerHalfSurfaceSpinMean]
  rw [<- spinProd_singleton]
  apply ghsvp_expJ_nonneg
  · exact fun _ _ => hbeta
  · intro v
    exact mul_nonneg hbeta (Nat.cast_nonneg _)


theorem isingCritical_oddPrismLowerHalfSurfaceSpinMean_tendsto_zero :
    Tendsto (oddPrismLowerHalfSurfaceSpinMean (Ising.betaC 3))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      oddPrismLowerHalfSurfaceSpinMean_nonneg
        (Ising.betaC 3) isingBetaC_three_pos.le n
  · exact Filter.Eventually.of_forall fun n =>
      oddPrismLowerHalfSurfaceSpinMean_le_plus
        (Ising.betaC 3) isingBetaC_three_pos.le n
  · exact isingCritical_oddPrismPlusCenter_tendsto_zero


end
end StatMech.FrontierA
