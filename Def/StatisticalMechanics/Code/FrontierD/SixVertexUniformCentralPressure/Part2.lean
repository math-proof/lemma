module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceParticleHole
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUniformCentralPressure.Part2
open Finset Matrix Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexPositiveEvenHeightCentralTraceMaximal
    (N : Nat) (c : Real) : Prop :=
  forall M n : Nat, n <= N ->
    Matrix.trace (sixVertexSectorTransfer N n c ^
        sixVertexPositiveEvenHeight M) <=
      Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^
        sixVertexPositiveEvenHeight M)

end
end StatMech.FrontierD
