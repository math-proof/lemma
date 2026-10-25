/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Mathlib.Algebra.Polynomial.Eval.Degree
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion.Part7
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

open Polynomial


theorem
    SixVertexMarkedAntidiagonalSuffixNonnegative.coefficientwiseLogConcave
    {N M n : Nat}
    (h : SixVertexMarkedAntidiagonalSuffixNonnegative N M n) :
    SixVertexMarkedTraceCoefficientwiseLogConcave N M n := by
  intro k
  rw [coeff_sixVertexMarkedTraceLogConcavityDifference_eq_sum_range]
  have hk := h k 0 (Nat.zero_le k)
  simpa using hk


theorem Polynomial.eval_nonneg_of_coeff_nonneg
    (p : Real[X]) (t : Real) (ht : 0 <= t)
    (hcoeff : forall k, 0 <= p.coeff k) :
    0 <= p.eval t := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (hcoeff k) (pow_nonneg ht k)


theorem sixVertexSectorTrace_logConcave_of_markedCoefficientwise
    (N M n : Nat) {c : Real} (hc : 2 <= c)
    (hcoeff : SixVertexMarkedTraceCoefficientwiseLogConcave N M n) :
    Matrix.trace (sixVertexSectorTransfer N (n - 1) c ^ M) *
        Matrix.trace (sixVertexSectorTransfer N (n + 1) c ^ M) <=
      Matrix.trace (sixVertexSectorTransfer N n c ^ M) ^ 2 := by
  let t := c - 2
  have ht : 0 <= t := by dsimp [t]; linarith
  have hnonneg := Polynomial.eval_nonneg_of_coeff_nonneg
    (sixVertexMarkedTraceLogConcavityDifference N M n) t ht hcoeff
  rw [eval_sixVertexMarkedTraceLogConcavityDifference] at hnonneg
  have hct : 2 + t = c := by dsimp [t]; ring
  rw [hct] at hnonneg
  linarith


theorem sixVertexSectorTraceLogConcave_of_markedCoefficientwise
    (N : Nat) {c : Real} (hc : 2 <= c)
    (hcoeff : forall M n : Nat, 0 < M -> 0 < n -> n < N ->
      SixVertexMarkedTraceCoefficientwiseLogConcave N M n) :
    SixVertexSectorTraceLogConcave N c := by
  intro M n hM hn0 hnN
  rw [sixVertexSectorTraceProfile_eq (by omega),
    sixVertexSectorTraceProfile_eq (by omega),
    sixVertexSectorTraceProfile_eq (by omega)]
  exact sixVertexSectorTrace_logConcave_of_markedCoefficientwise
    N M n hc (hcoeff M n hM hn0 hnN)

end
end StatMech.FrontierD
