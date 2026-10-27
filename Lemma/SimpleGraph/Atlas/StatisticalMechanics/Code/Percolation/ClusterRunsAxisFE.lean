import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.ClusterRunsAxisFE.Part2
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[craf_mem_corridorEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterRunsAxisFE.lean)
-/
@[path]
private lemma craf_mem_corridorEdges_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {t : ℕ}
-- given
  (ht : t < L) :
-- imply
  s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) ∈ hrHD_corridorEdges j (L + 1) := by
-- proof
  apply StatMech.Percolation.craf_mem_corridorEdges j L ht

/--
[craf_corridor_axis_edge_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterRunsAxisFE.lean)
-/
@[path]
private lemma craf_corridor_axis_edge_open_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {t : ℕ}
-- given
  (ht : t < L) :
-- imply
  forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true := by
-- proof
  apply StatMech.Percolation.craf_corridor_axis_edge_open ω j L ht

/--
[craf_clusterRunsAlongAxis_of_insertion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterRunsAxisFE.lean)
-/
@[path]
private lemma craf_clusterRunsAlongAxis_of_insertion_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : craf_AxisRoutingPremise ω x j L) :
-- imply
  crr_ClusterRunsAlongAxis (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j := by
-- proof
  apply StatMech.Percolation.craf_clusterRunsAlongAxis_of_insertion ω x j L h

/--
[craf_axisAssignment_of_insertion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterRunsAxisFE.lean)
-/
@[path]
private lemma craf_axisAssignment_of_insertion_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : craf_AxisRoutingPremise ω x j L) :
-- imply
  crr_AxisAssignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j := by
-- proof
  apply StatMech.Percolation.craf_axisAssignment_of_insertion ω x j L h

/--
[craf_clusterReachesRay_of_insertion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterRunsAxisFE.lean)
-/
@[path]
private lemma craf_clusterReachesRay_of_insertion_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : craf_AxisRoutingPremise ω x j L) :
-- imply
  lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j := by
-- proof
  apply StatMech.Percolation.craf_clusterReachesRay_of_insertion ω x j L h

/--
[craf_axisRoutingPremise_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterRunsAxisFE.lean)
-/
@[path]
private lemma craf_axisRoutingPremise_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) (hrHD_rayPt j 1)).Infinite) :
-- imply
  craf_AxisRoutingPremise ω (hrHD_rayPt j 1) j L := by
-- proof
  apply StatMech.Percolation.craf_axisRoutingPremise_neighbour ω j L hinf

/--
[craf_axisAssignment_of_neighbour_insertion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterRunsAxisFE.lean)
-/
@[path]
private lemma craf_axisAssignment_of_neighbour_insertion_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) (hrHD_rayPt j 1)).Infinite) :
-- imply
  crr_AxisAssignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1) j := by
-- proof
  apply StatMech.Percolation.craf_axisAssignment_of_neighbour_insertion ω j L hinf

/--
[craf_someAxis_reach_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterRunsAxisFE.lean)
-/
@[path]
private lemma craf_someAxis_reach_of_infinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d ω x).Infinite) :
-- imply
  ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y := by
-- proof
  apply StatMech.Percolation.craf_someAxis_reach_of_infinite ω x hinf n


-- created on 2026-10-23
