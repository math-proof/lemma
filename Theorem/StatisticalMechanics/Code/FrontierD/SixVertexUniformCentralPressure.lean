/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceParticleHole
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorTrace_particleHole_uniformPressure
    {N n : Nat} (hn : n <= N) (M : Nat) (c : Real) :
    Matrix.trace (sixVertexSectorTransfer N (N - n) c ^ M) =
      Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  have hpoly := congrArg (Polynomial.eval (c - 2))
    (sixVertexShiftedSectorTracePolynomial_particleHole hn M)
  simpa [eval_sixVertexShiftedSectorTracePolynomial] using hpoly

theorem sixVertexCentralTrace_le_fixedWidthPartitionSum
    (N M : Nat) (hM : 0 < M)
    {c : Real} (hc : 0 < c) :
    Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M) <=
      sixVertexFixedWidthPartitionSum N M c := by
  rw [sixVertexFixedWidthPartitionSum_eq_sum_sector_traces N M hM]
  let middle : Fin (N + 1) :=
    ⟨N / 2, Nat.lt_succ_of_le (Nat.div_le_self N 2)⟩
  change Matrix.trace
      (sixVertexSectorTransfer N middle.val c ^ M) <= _
  exact Finset.single_le_sum
    (s := Finset.univ)
    (fun sector (_ : sector ∈ (Finset.univ : Finset (Fin (N + 1)))) =>
      (sixVertexSector_trace_pow_pos (by omega) hc M).le)
    (Finset.mem_univ middle)

theorem sixVertexBalancedTraceShare_mem_Ioc
    (N M : Nat) (hM : 0 < M)
    {c : Real} (hc : 0 < c) :
    sixVertexBalancedTraceShare N M c ∈ Set.Ioc 0 1 := by
  have hcentral : 0 < Matrix.trace
      (sixVertexSectorTransfer N (N / 2) c ^ M) :=
    sixVertexSector_trace_pow_pos (Nat.div_le_self N 2) hc M
  have hfull : 0 < sixVertexFixedWidthPartitionSum N M c :=
    sixVertexFixedWidthPartitionSum_pos N M hM hc
  constructor
  · exact div_pos hcentral hfull
  · rw [sixVertexBalancedTraceShare, div_le_one hfull]
    exact sixVertexCentralTrace_le_fixedWidthPartitionSum N M hM hc


end
end StatMech.FrontierD
