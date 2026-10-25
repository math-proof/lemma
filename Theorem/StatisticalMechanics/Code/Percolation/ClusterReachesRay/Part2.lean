/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Def.StatisticalMechanics.Code.Percolation.ClusterReachesRay
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem crr_clusterReachesRay_of_runsAlongAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : crr_ClusterRunsAlongAxis ω x j) :
    lma_ClusterReachesRay ω x j := by
  obtain ⟨L, hopen, hxe1, hxe1', hinf⟩ := h
  refine ⟨L, ?_, crr_corridor_internal ω x j L hxe1 hopen, ?_, hinf⟩
  · rw [mem_cluster]; exact hxe1
  · 
    have hfar : Connected d (removeSite 0 ω) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) :=
      crr_axisOpen_connected_removeSite ω j L hopen L le_rfl
    exact (hxe1'.trans hfar).symm


theorem crr_runsAlongAxis_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    crr_ClusterRunsAlongAxis ω (hrHD_rayPt j 1) j := by
  refine ⟨0, ?_, connected_rfl, connected_rfl, hinf⟩
  intro t ht; omega


theorem crr_clusterReachesRay_of_neighbour' (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    lma_ClusterReachesRay ω (hrHD_rayPt j 1) j :=
  crr_clusterReachesRay_of_runsAlongAxis ω (hrHD_rayPt j 1) j
    (crr_runsAlongAxis_of_neighbour ω j hinf)


end Percolation
end StatMech
