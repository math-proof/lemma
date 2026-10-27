import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc_cutmeetsaxis
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc_cutMeetsAxis_iff_clusterMeetsCorridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_cutMeetsAxis_iff_clusterMeetsCorridor_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ} :
-- imply
  bc_CutMeetsAxis ω x j L ↔ cnp_ClusterMeetsCorridor ω x j L := by
-- proof
  apply StatMech.Walls.bc_cutMeetsAxis_iff_clusterMeetsCorridor ω x j L

/--
[bc_clusterMeetsCorridor_of_cutMeetsAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_clusterMeetsCorridor_of_cutMeetsAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : bc_CutMeetsAxis ω x j L) :
-- imply
  cnp_ClusterMeetsCorridor ω x j L := by
-- proof
  apply StatMech.Walls.bc_clusterMeetsCorridor_of_cutMeetsAxis ω x j L h

/--
[bc_cutMeetsAxis_meets_corridorCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_cutMeetsAxis_meets_corridorCell_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : bc_CutMeetsAxis ω x j L) :
-- imply
  ∃ m : ℕ, 1 ≤ m ∧ m ≤ L + 1 ∧ Connected d (removeSite 0 ω) x (hrHD_rayPt j (m : ℤ)) := by
-- proof
  apply StatMech.Walls.bc_cutMeetsAxis_meets_corridorCell ω h

/--
[bc_cutMeetsAxis_cluster_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_cutMeetsAxis_cluster_infinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : bc_CutMeetsAxis ω x j L) :
-- imply
  (cluster d (removeSite 0 ω) x).Infinite := by
-- proof
  apply StatMech.Walls.bc_cutMeetsAxis_cluster_infinite ω h

/--
[bc_cutMeetsAxis_witness_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_cutMeetsAxis_witness_ne_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : bc_CutMeetsAxis ω x j L) :
-- imply
  x ≠ 0 := by
-- proof
  apply StatMech.Walls.bc_cutMeetsAxis_witness_ne_zero ω h

/--
[bc_cutMeetsAxis_corridorCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_cutMeetsAxis_corridorCell_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {m : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hmL : m ≤ L + 1)
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j (m : ℤ))).Infinite) :
-- imply
  bc_CutMeetsAxis ω (hrHD_rayPt j (m : ℤ)) j L := by
-- proof
  apply StatMech.Walls.bc_cutMeetsAxis_corridorCell ω j L m hm1 hmL hinf

/--
[bc_cutMeetsAxis_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_cutMeetsAxis_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  bc_CutMeetsAxis ω (hrHD_rayPt j 1) j L := by
-- proof
  apply StatMech.Walls.bc_cutMeetsAxis_neighbour ω j L hinf

/--
[bc_cut_someAxis_reach_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_cut_someAxis_reach_of_infinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Walls.bc_cut_someAxis_reach_of_infinite ω x hinf n

/--
[bc_axisRoutingPremise_of_cutMeetsAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_axisRoutingPremise_of_cutMeetsAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : bc_CutMeetsAxis ω x j L) :
-- imply
  craf_AxisRoutingPremise ω x j L := by
-- proof
  apply StatMech.Walls.bc_axisRoutingPremise_of_cutMeetsAxis ω x j L h

/--
[bc_axisAssignment_of_cutMeetsAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_axisAssignment_of_cutMeetsAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : bc_CutMeetsAxis ω x j L) :
-- imply
  crr_AxisAssignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j := by
-- proof
  apply StatMech.Walls.bc_axisAssignment_of_cutMeetsAxis ω x j L h

/--
[bc_clusterReachesRay_of_cutMeetsAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_clusterReachesRay_of_cutMeetsAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : bc_CutMeetsAxis ω x j L) :
-- imply
  lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j := by
-- proof
  apply StatMech.Walls.bc_clusterReachesRay_of_cutMeetsAxis ω x j L h

/--
[bc_cut_meets_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_cutmeetsaxis.lean)
-/
@[path]
private lemma bc_cut_meets_axis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ} :
-- imply
  ((cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite → bc_CutMeetsAxis ω (hrHD_rayPt j 1) j L) ∧ (∀ x : Site d, bc_CutMeetsAxis ω x j L → craf_AxisRoutingPremise ω x j L ∧ x ≠ 0) := by
-- proof
  apply StatMech.Walls.bc_cut_meets_axis ω j L


-- created on 2026-10-23
