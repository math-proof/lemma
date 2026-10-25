/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseBoundaryGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenContractionGeneral
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
import Theorem.StatisticalMechanics.Code.Walls.bc63coarseforest.Part2
import Def.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundaryGeneral.Part2
open Finset Set SimpleGraph


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}


@[simp] theorem mem_bgfdFaithfulAllOpenTrifIndicesInBox
    {omega : ConfigSpace (Sym2 (Site d))} {L N : ℕ} {j : Site d} :
    j ∈ bgfdFaithfulAllOpenTrifIndicesInBox omega L N ↔
      j ∈ box d N ∧ BgfdFaithfulAllOpenTrifAt omega L j := by
  classical
  simp [bgfdFaithfulAllOpenTrifIndicesInBox]


theorem bgfdFaithfulAllOpenTrifIndicesInBox_count
    (omega : ConfigSpace (Sym2 (Site d))) (L N : ℕ) :
    (bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card ≤
      (vertexBoundary_finite d
        ((2 * L + 1) * N + L + 1)).toFinset.card := by
  apply bgfdFaithfulAllOpenTrifAt_count_inner omega L ((2 * L + 1) * N)
  · intro j hj
    exact (mem_bgfdFaithfulAllOpenTrifIndicesInBox.mp hj).2
  · intro j hj
    exact bgfd_centre_mem_scaled_box
      (mem_bgfdFaithfulAllOpenTrifIndicesInBox.mp hj).1


end StatMech.FrontierA
