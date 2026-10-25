/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Mathlib.Algebra.Polynomial.Eval.Degree
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion.Part4
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

open Polynomial


theorem sixVertexMarkedSectorTraceCoefficient_nonneg
    (N M n k : Nat) :
    0 <= sixVertexMarkedSectorTraceCoefficient N M n k := by
  unfold sixVertexMarkedSectorTraceCoefficient
  apply (show Polynomial.CoeffNonnegative
      (sixVertexShiftedSectorTracePolynomial N M n) from ?_)
  unfold sixVertexShiftedSectorTracePolynomial Matrix.trace
  apply Polynomial.coeffNonnegative_sum
  intro x hx
  exact sixVertexShiftedSectorTransferPolynomial_pow_coeffNonnegative
    N n M x x


end
end StatMech.FrontierD
