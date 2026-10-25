/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Mathlib.Algebra.Polynomial.Eval.Degree
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion.Part5
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

open Polynomial


noncomputable def sixVertexMarkedTraceLogConcavityDifference
    (N M n : Nat) : Real[X] :=
  sixVertexShiftedSectorTracePolynomial N M n ^ 2 -
    sixVertexShiftedSectorTracePolynomial N M (n - 1) *
      sixVertexShiftedSectorTracePolynomial N M (n + 1)

end
end StatMech.FrontierD
