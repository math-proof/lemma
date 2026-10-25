/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Mathlib.Algebra.Polynomial.Eval.Degree
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

open Polynomial


theorem eval_sixVertexShiftedSectorTracePolynomial
    (N M n : Nat) (t : Real) :
    eval t (sixVertexShiftedSectorTracePolynomial N M n) =
      Matrix.trace (sixVertexSectorTransfer N n (2 + t) ^ M) := by
  unfold sixVertexShiftedSectorTracePolynomial
  change (evalRingHom t)
      (Matrix.trace (sixVertexShiftedSectorTransferPolynomial N n ^ M)) = _
  rw [AddMonoidHom.map_trace, Matrix.map_pow,
    map_sixVertexShiftedSectorTransferPolynomial]


end
end StatMech.FrontierD
