/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part6
open Finset Matrix


namespace StatMech.FrontierD

theorem sixVertexPeriodicRowsFixedSectorEquiv_weight
    (N M : ℕ) (hM : 0 < M) (c : ℝ) (n : Fin (N + 1))
    (x : SixVertexPeriodicRowsInSector N M hM c n) :
    sixVertexPeriodicRowWeight hM c x.1 =
      matrixCycleWeight hM (sixVertexSectorTransfer N n c)
        (sixVertexPeriodicRowsFixedSectorEquiv N M hM c n x) := by
  rw [sixVertexPeriodicRowWeight, matrixCycleWeight, matrixCycleWeight]
  apply Finset.prod_congr rfl
  intro i hi
  change sixVertexTransfer N c (x.1.1 i)
    (x.1.1 (finitePeriodicSucc hM i)) = _
  simp [sixVertexPeriodicRowsFixedSectorEquiv, sixVertexSectorTransfer]


theorem sixVertexPeriodicRowPartitionSum_eq_trace
    (N M : ℕ) (hM : 0 < M) (c : ℝ) :
    sixVertexPeriodicRowPartitionSum N M hM c =
      Matrix.trace (sixVertexTransfer N c ^ M) := by
  exact matrixCompatibleCycleSum_eq_trace_pow hM (sixVertexTransfer N c)


theorem sixVertexPeriodicRowPartitionSum_eq_sum_sector_traces
    (N M : ℕ) (hM : 0 < M) (c : ℝ) :
    sixVertexPeriodicRowPartitionSum N M hM c =
      ∑ n : Fin (N + 1), Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  rw [sixVertexPeriodicRowPartitionSum]
  calc
    ∑ x : SixVertexPeriodicRows N M hM c, sixVertexPeriodicRowWeight hM c x =
        ∑ nx : Σ n : Fin (N + 1),
          SixVertexPeriodicRowsInSector N M hM c n,
            sixVertexPeriodicRowWeight hM c nx.2.1 := by
      apply Fintype.sum_equiv (sixVertexPeriodicRowsLabelEquiv N M hM c)
      intro x
      rfl
    _ = ∑ n : Fin (N + 1),
        ∑ x : SixVertexPeriodicRowsInSector N M hM c n,
          sixVertexPeriodicRowWeight hM c x.1 := by
      rw [Fintype.sum_sigma]
    _ = ∑ n : Fin (N + 1),
        ∑ y : MatrixCompatibleCycle hM (sixVertexSectorTransfer N n c),
          matrixCycleWeight hM (sixVertexSectorTransfer N n c) y := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Fintype.sum_equiv (sixVertexPeriodicRowsFixedSectorEquiv N M hM c n)
      exact sixVertexPeriodicRowsFixedSectorEquiv_weight N M hM c n
    _ = ∑ n : Fin (N + 1),
        matrixCompatibleCycleSum hM (sixVertexSectorTransfer N n c) := by
      rfl
    _ = ∑ n : Fin (N + 1),
        Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact matrixCompatibleCycleSum_eq_trace_pow hM _


end StatMech.FrontierD
