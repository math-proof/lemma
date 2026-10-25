/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexWidthFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergy
import Def.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part2
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

theorem sixVertexFixedWidthPartitionSum_eq_periodicRows
    (N M : ℕ) (hM : 0 < M) (c : ℝ) :
    sixVertexFixedWidthPartitionSum N M c =
      sixVertexPeriodicRowPartitionSum N M hM c := by
  exact (sixVertexPeriodicRowPartitionSum_eq_trace N M hM c).symm


theorem sixVertexFixedWidthPartitionSum_eq_sum_sector_traces
    (N M : ℕ) (hM : 0 < M) (c : ℝ) :
    sixVertexFixedWidthPartitionSum N M c =
      ∑ n : Fin (N + 1), Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  rw [sixVertexFixedWidthPartitionSum_eq_periodicRows N M hM c]
  exact sixVertexPeriodicRowPartitionSum_eq_sum_sector_traces N M hM c


theorem sixVertexFixedWidthPartitionSum_pos
    (N M : ℕ) (hM : 0 < M) {c : ℝ} (hc : 0 < c) :
    0 < sixVertexFixedWidthPartitionSum N M c := by
  rw [sixVertexFixedWidthPartitionSum_eq_sum_sector_traces N M hM c]
  apply Finset.sum_pos'
  · intro n hn
    exact (sixVertexSector_trace_pow_pos (sixVertexWidthSectorIndex_le N n) hc M).le
  · let n : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
    exact ⟨n, Finset.mem_univ n,
      sixVertexSector_trace_pow_pos (sixVertexWidthSectorIndex_le N n) hc M⟩


end StatMech.FrontierD
