/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorPerronLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCentralSectorDominance.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorPerronProfile_eq
    {N n : Nat} (hn : n <= N) (c : Real) :
    sixVertexSectorPerronProfile N c n =
      sixVertexSectorTopEigenvalue N n hn c := by
  simp [sixVertexSectorPerronProfile, min_eq_left hn]

theorem sixVertexSectorPerronProfile_pos
    {N n : Nat} (hn : n <= N) {c : Real} (hc : 0 < c) :
    0 < sixVertexSectorPerronProfile N c n := by
  rw [sixVertexSectorPerronProfile_eq hn]
  exact sixVertexSectorTopEigenvalue_pos hn hc

theorem sixVertexSectorPerronProfile_particleHole
    {N n : Nat} (hn : n <= N) (c : Real) :
    sixVertexSectorPerronProfile N c (N - n) =
      sixVertexSectorPerronProfile N c n := by
  rw [sixVertexSectorPerronProfile_eq (Nat.sub_le N n),
    sixVertexSectorPerronProfile_eq hn]
  exact sixVertexSectorTopEigenvalue_particleHole hn c


end
end StatMech.FrontierD
