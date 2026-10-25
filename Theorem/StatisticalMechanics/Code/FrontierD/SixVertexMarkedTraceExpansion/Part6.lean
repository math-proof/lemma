/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Mathlib.Algebra.Polynomial.Eval.Degree
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion.Part6
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

open Polynomial


theorem eval_sixVertexMarkedTraceLogConcavityDifference
    (N M n : Nat) (t : Real) :
    eval t (sixVertexMarkedTraceLogConcavityDifference N M n) =
      Matrix.trace (sixVertexSectorTransfer N n (2 + t) ^ M) ^ 2 -
        Matrix.trace (sixVertexSectorTransfer N (n - 1) (2 + t) ^ M) *
          Matrix.trace
            (sixVertexSectorTransfer N (n + 1) (2 + t) ^ M) := by
  simp [sixVertexMarkedTraceLogConcavityDifference,
    eval_sixVertexShiftedSectorTracePolynomial]


theorem coeff_sixVertexMarkedTraceLogConcavityDifference
    (N M n k : Nat) :
    (sixVertexMarkedTraceLogConcavityDifference N M n).coeff k =
      ∑ ij ∈ Finset.antidiagonal k,
        (sixVertexMarkedSectorTraceCoefficient N M n ij.1 *
            sixVertexMarkedSectorTraceCoefficient N M n ij.2 -
          sixVertexMarkedSectorTraceCoefficient N M (n - 1) ij.1 *
            sixVertexMarkedSectorTraceCoefficient N M (n + 1) ij.2) := by
  unfold sixVertexMarkedTraceLogConcavityDifference
  simp only [pow_two, Polynomial.coeff_sub, Polynomial.coeff_mul,
    sixVertexMarkedSectorTraceCoefficient]
  rw [Finset.sum_sub_distrib]

theorem coeff_sixVertexMarkedTraceLogConcavityDifference_eq_sum_range
    (N M n k : Nat) :
    (sixVertexMarkedTraceLogConcavityDifference N M n).coeff k =
      ∑ i ∈ Finset.range (k + 1),
        (sixVertexMarkedSectorTraceCoefficient N M n i *
            sixVertexMarkedSectorTraceCoefficient N M n (k - i) -
          sixVertexMarkedSectorTraceCoefficient N M (n - 1) i *
            sixVertexMarkedSectorTraceCoefficient N M (n + 1) (k - i)) := by
  rw [coeff_sixVertexMarkedTraceLogConcavityDifference]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk _ k


end
end StatMech.FrontierD
