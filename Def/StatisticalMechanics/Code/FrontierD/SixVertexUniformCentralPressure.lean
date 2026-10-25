/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceParticleHole
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUniformCentralPressure
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexUniformHeightCentralTraceBound
    (N : Nat) (c : Real) : Prop :=
  exists C : Real, 0 < C ∧ forall M : Nat, 0 < M ->
    sixVertexFixedWidthPartitionSum N M c <=
      C * Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M)


def SixVertexAllHeightCentralTraceMaximal (N : Nat) (c : Real) : Prop :=
  forall M n : Nat, 0 < M -> n <= N ->
    Matrix.trace (sixVertexSectorTransfer N n c ^ M) <=
      Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M)

end
end StatMech.FrontierD
