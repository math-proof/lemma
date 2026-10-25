/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Mathlib.Algebra.Polynomial.Eval.Degree
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion.Part6
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

open Polynomial


def SixVertexMarkedAntidiagonalSuffixNonnegative
    (N M n : Nat) : Prop :=
  forall k r : Nat, r <= k ->
    0 <= ∑ i ∈ (Finset.range (k + 1)).filter (fun i => r <= i),
      (sixVertexMarkedSectorTraceCoefficient N M n i *
          sixVertexMarkedSectorTraceCoefficient N M n (k - i) -
        sixVertexMarkedSectorTraceCoefficient N M (n - 1) i *
          sixVertexMarkedSectorTraceCoefficient N M (n + 1) (k - i))


def SixVertexMarkedTraceCoefficientwiseLogConcave
    (N M n : Nat) : Prop :=
  forall k, 0 <=
    (sixVertexMarkedTraceLogConcavityDifference N M n).coeff k

end
end StatMech.FrontierD
