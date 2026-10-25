/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc15core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc14core.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ClusterRunsAxisFE.Part2
import Def.StatisticalMechanics.Code.Walls.bc15core.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc15_nearReach_of_cutNearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : bc15_CutNearReach ω x j) :
    bc15_NearAxisReach ω x j := by
  obtain ⟨hcut, hinf⟩ := h
  exact ⟨bc15_connected_of_cut ω x j hcut, hcut, hinf⟩


theorem bc15_cutNearReach_of_nearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : bc15_NearAxisReach ω x j) :
    bc15_CutNearReach ω x j := by
  obtain ⟨_hω, hcut, hinf⟩ := h
  exact ⟨hcut, hinf⟩


theorem bc15_runsAlong_iff_cutNearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) :
    crr_ClusterRunsAlongAxis ω x j ↔ bc15_CutNearReach ω x j :=
  ⟨fun h => bc15_cutNearReach_of_nearReach ω x j (bc15_nearReach_of_runsAlongAxis ω x j h),
    fun h => bc15_runsAlongAxis_of_nearReach ω x j (bc15_nearReach_of_cutNearReach ω x j h)⟩


theorem bc15_runsAlongAxis_of_cutNearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : bc15_CutNearReach ω x j) :
    crr_ClusterRunsAlongAxis ω x j :=
  (bc15_runsAlong_iff_cutNearReach ω x j).mpr h


end Walls
end StatMech
