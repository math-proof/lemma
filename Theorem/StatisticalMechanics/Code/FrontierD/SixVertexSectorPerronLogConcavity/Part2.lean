/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCentralSectorDominance.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part2
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorTraceProfile_eq
    {N M n : Nat} (hn : n <= N) (c : Real) :
    sixVertexSectorTraceProfile N M c n =
      Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  unfold sixVertexSectorTraceProfile
  rw [min_eq_left hn]


end
end StatMech.FrontierD
