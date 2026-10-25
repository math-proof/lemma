/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part8
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


theorem fvWeight_eq_endpointFactor_mul_transferProduct
    (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (beta h : ℝ) :
    fvWeight eta n (bondFinsetTouch 1 n) beta h tau =
      Real.exp (-(beta * h / 2) *
        (transferSpin (fvPathState eta n tau 0) +
          transferSpin (fvPathState eta n tau (2 * n + 2)))) *
        fvTransferProduct eta n tau beta h := by
  unfold fvWeight fvEnergy fvTransferProduct
  simp_rw [isingTransferReal_apply]
  rw [← Real.exp_sum, ← Real.exp_add]
  rw [sum_bondFinsetTouch_eq_path, sum_boxFinset_eq_path]
  rw [Finset.sum_add_distrib]
  have hbondfactor :
      (∑ k ∈ Finset.range (2 * n + 2),
        beta * transferSpin (fvPathState eta n tau k) *
          transferSpin (fvPathState eta n tau (k + 1))) =
        beta * ∑ k ∈ Finset.range (2 * n + 2),
          transferSpin (fvPathState eta n tau k) *
            transferSpin (fvPathState eta n tau (k + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hbondfactor, ← Finset.mul_sum]
  have hhalf := sum_adjacent_half
    (fun k => transferSpin (fvPathState eta n tau k)) (2 * n + 1)
  rw [← Finset.sum_div] at hhalf
  have hfield :
      (∑ k ∈ Finset.range (2 * n + 2),
        (transferSpin (fvPathState eta n tau k) +
          transferSpin (fvPathState eta n tau (k + 1)))) =
        transferSpin (fvPathState eta n tau 0) +
          transferSpin (fvPathState eta n tau (2 * n + 2)) +
            2 * ∑ k ∈ Finset.range (2 * n + 1),
              transferSpin (fvPathState eta n tau (k + 1)) := by
    linarith
  rw [hfield]
  congr 1
  ring


end StatMech.FrontierB
