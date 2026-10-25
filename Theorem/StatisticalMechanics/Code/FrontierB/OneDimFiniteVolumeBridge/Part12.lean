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
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part12
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma fvWeight_eq_endpointFactor_mul_openProduct
    (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) (beta h : ℝ) :
    fvWeight eta n (bondFinsetTouch 1 n) beta h tau =
      fvEndpointFactor eta n beta h * fvTransferProduct eta n tau beta h := by
  rw [fvWeight_eq_endpointFactor_mul_transferProduct]
  unfold fvEndpointFactor
  rw [fvPathState_zero, fvPathState_right]


theorem fvZ_eq_endpointFactor_mul_matrix_pow
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) :
    fvZ eta n (bondFinsetTouch 1 n) beta h =
      fvEndpointFactor eta n beta h *
        (isingTransferReal beta (beta * h) ^ (2 * n + 2))
          (fvLeftBoundaryState eta n) (fvRightBoundaryState eta n) := by
  unfold fvZ
  simp_rw [fvWeight_eq_endpointFactor_mul_openProduct]
  rw [← Finset.mul_sum, sum_fvTransferProduct_eq_matrix_pow]


end StatMech.FrontierB
