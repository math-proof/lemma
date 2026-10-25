/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexSectorPositiveEvenTraceLogConcave
    (N : Nat) (c : Real) : Prop :=
  forall M n : Nat, 0 < n -> n < N ->
    Matrix.trace
          (sixVertexSectorTransfer N (n - 1) c ^
            sixVertexPositiveEvenHeight M) *
        Matrix.trace
          (sixVertexSectorTransfer N (n + 1) c ^
            sixVertexPositiveEvenHeight M) <=
      Matrix.trace
          (sixVertexSectorTransfer N n c ^
            sixVertexPositiveEvenHeight M) ^ 2


end
end StatMech.FrontierD
