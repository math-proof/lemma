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
import Def.StatisticalMechanics.Code.Walls.bc15core
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc15_runsAlongAxis_of_nearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : bc15_NearAxisReach ω x j) :
    crr_ClusterRunsAlongAxis ω x j := by
  obtain ⟨hnear, hnearCut, hinf⟩ := h
  exact ⟨0, fun t ht => absurd ht (by omega), hnear, hnearCut, hinf⟩


theorem bc15_nearReach_of_runsAlongAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : crr_ClusterRunsAlongAxis ω x j) :
    bc15_NearAxisReach ω x j := by
  obtain ⟨L, _hopen, hnear, hnearCut, hinf⟩ := h
  exact ⟨hnear, hnearCut, hinf⟩


theorem bc15_runsAlong_iff_nearReach (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) :
    crr_ClusterRunsAlongAxis ω x j ↔ bc15_NearAxisReach ω x j :=
  ⟨bc15_nearReach_of_runsAlongAxis ω x j, bc15_runsAlongAxis_of_nearReach ω x j⟩


theorem bc15_connected_of_cut (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d)
    (h : Connected d (removeSite 0 ω) x (hrHD_rayPt j 1)) :
    Connected d ω x (hrHD_rayPt j 1) :=
  connected_mono (removeSite_le 0 ω) h


end Walls
end StatMech
