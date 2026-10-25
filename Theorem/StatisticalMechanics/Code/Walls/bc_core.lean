/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ClusterRunsAxisFE.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc_cutmeetsaxis
import Theorem.StatisticalMechanics.Code.Walls.bc_mouthcorridor
import Theorem.StatisticalMechanics.Code.Walls.bc_raydisjoint
import Theorem.StatisticalMechanics.Code.Walls.bc_forcemono
import Def.StatisticalMechanics.Code.Walls.bc_core
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc_nearAxis_of_axisAssignment (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : crr_AxisAssignment ω x j) : bc_NearAxis ω x j := by
  obtain ⟨L, _, hnear, hcut, hinf⟩ := h
  exact ⟨mem_cluster.mpr hnear, hcut.symm, hinf⟩


theorem bc_clusterReachesRay_of_nearAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : bc_NearAxis ω x j) : lma_ClusterReachesRay ω x j := by
  obtain ⟨hmem, hreach, hinf⟩ := h
  refine ⟨0, hmem, ?_, ?_, hinf⟩
  · intro e he; simp [lma_corridorEdges] at he
  · have he : ((0 : ℕ) : ℤ) + 1 = (1 : ℤ) := by norm_num
    rw [he]; exact hreach


end Walls
end StatMech
