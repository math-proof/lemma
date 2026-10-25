/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman.Part3
open Filter Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

theorem criticalFiniteBoxGlobalParityFourthCumulant_eq_scalarFourthCumulant
    (d n : Nat) :
    criticalFiniteBoxGlobalParityFourthCumulant d n =
      scalarFourthCumulant
        (finiteParityTotalSpinFourthMoment
          (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1))
        (finiteParityTotalSpinSecondMoment
          (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)) := by
  unfold criticalFiniteBoxGlobalParityFourthCumulant
  exact (scalarFourthCumulant_finiteParityTotalSpin_eq_integrated
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)).symm

theorem criticalFiniteBoxGlobalParityFourthCumulant_bound
    (hd : 2 ≤ d) (n : Nat) :
    0 ≤ -criticalFiniteBoxGlobalParityFourthCumulant d n ∧
      -criticalFiniteBoxGlobalParityFourthCumulant d n ≤
        (Fintype.card (sctBox d n) : Real) *
          (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 +
            12 * criticalFreeBoxSusceptibility d (2 * n) ^ 2) := by
  have hbeta : 0 ≤ IsingFK.betaC (magnetization d) := by
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact (tildeBetaCIsing_pos hd).le
  have hroot (i : sctBox d n) :
      0 ≤ -finiteParityIntegratedFourthCumulant
          (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i ∧
        -finiteParityIntegratedFourthCumulant
            (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i ≤
          2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 +
            12 * criticalFreeBoxSusceptibility d (2 * n) ^ 2 :=
    finiteParityIntegratedFourthCumulant_treeDiagram_bound
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
      hbeta (fun _ => by norm_num) (criticalFreeBoxSusceptibility d (2 * n))
      (criticalFreeBoxSusceptibility_nonneg hd (2 * n))
      (criticalFiniteBoxRowSusceptibility_le hd n) i
  have hneg : -criticalFiniteBoxGlobalParityFourthCumulant d n =
      ∑ i : sctBox d n,
        -finiteParityIntegratedFourthCumulant
          (sctBoxGraph d n) (IsingFK.betaC (magnetization d))
            (fun _ => 1) i := by
    unfold criticalFiniteBoxGlobalParityFourthCumulant
    rw [Finset.sum_neg_distrib]
  rw [hneg]
  constructor
  · exact Finset.sum_nonneg fun i _ => (hroot i).1
  · calc
      _ ≤ ∑ _i : sctBox d n,
          (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 +
            12 * criticalFreeBoxSusceptibility d (2 * n) ^ 2) := by
        exact Finset.sum_le_sum fun i _ => (hroot i).2
      _ = (Fintype.card (sctBox d n) : Real) *
          (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 4 +
            12 * criticalFreeBoxSusceptibility d (2 * n) ^ 2) := by
        simp [nsmul_eq_mul]
        ring


end
end StatMech.FrontierA
