/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterRunsAxisFE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
import Def.StatisticalMechanics.Code.Percolation.ClusterRunsAxisFE
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem craf_clusterRunsAlongAxis_of_insertion (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (L : ℕ) (h : craf_AxisRoutingPremise ω x j L) :
    crr_ClusterRunsAlongAxis (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j := by
  obtain ⟨hnear, hnearCut, hinf⟩ := h
  exact ⟨L, fun t ht => craf_corridor_axis_edge_open ω j L ht, hnear, hnearCut, hinf⟩


theorem craf_axisAssignment_of_insertion (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (L : ℕ) (h : craf_AxisRoutingPremise ω x j L) :
    crr_AxisAssignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  craf_clusterRunsAlongAxis_of_insertion ω x j L h


theorem craf_clusterReachesRay_of_insertion (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (L : ℕ) (h : craf_AxisRoutingPremise ω x j L) :
    lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j :=
  crr_clusterReachesRay_of_assignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j
    (craf_axisAssignment_of_insertion ω x j L h)


theorem craf_axisRoutingPremise_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    craf_AxisRoutingPremise ω (hrHD_rayPt j 1) j L :=
  ⟨connected_rfl, connected_rfl, hinf⟩


theorem craf_axisAssignment_of_neighbour_insertion (ω : ConfigSpace (Sym2 (Site d)))
    (j : Fin d) (L : ℕ)
    (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))
      (hrHD_rayPt j 1)).Infinite) :
    crr_AxisAssignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1) j :=
  craf_axisAssignment_of_insertion ω (hrHD_rayPt j 1) j L
    (craf_axisRoutingPremise_neighbour ω j L hinf)


theorem craf_someAxis_reach_of_infinite (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d ω x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y :=
  crr_infinite_reaches_far_coord ω x hinf n

end Percolation
end StatMech
