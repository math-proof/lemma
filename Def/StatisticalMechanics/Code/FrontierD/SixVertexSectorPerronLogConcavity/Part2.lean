module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCentralSectorDominance.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity
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

def SixVertexSectorPerronLogConcave (N : Nat) (c : Real) : Prop :=
  forall n : Nat, 0 < n -> n < N ->
    sixVertexSectorPerronProfile N c (n - 1) *
        sixVertexSectorPerronProfile N c (n + 1) <=
      sixVertexSectorPerronProfile N c n ^ 2


noncomputable def sixVertexSectorTraceProfile
    (N M : Nat) (c : Real) (n : Nat) : Real :=
  Matrix.trace
    (sixVertexSectorTransfer N (min n N) c ^ M)

end
end StatMech.FrontierD
