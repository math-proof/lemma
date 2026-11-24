module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCentralSectorDominance.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part2
open Finset Matrix Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexSectorTraceLogConcave (N : Nat) (c : Real) : Prop :=
  forall M n : Nat, 0 < M -> 0 < n -> n < N ->
    sixVertexSectorTraceProfile N M c (n - 1) *
        sixVertexSectorTraceProfile N M c (n + 1) <=
      sixVertexSectorTraceProfile N M c n ^ 2


end
end StatMech.FrontierD
