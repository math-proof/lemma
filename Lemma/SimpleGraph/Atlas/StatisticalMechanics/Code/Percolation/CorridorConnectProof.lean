import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.CorridorConnectProof
open MeasureTheory Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Combinatorics StatMech StatMech.Percolation


/--
[cnp_mouth_connected_corridorCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_mouth_connected_corridorCell_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {m : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hmL : m ≤ L + 1) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) := by
-- proof
  apply StatMech.Percolation.cnp_mouth_connected_corridorCell ω j L m hm1 hmL

/--
[cnp_removeSite_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_removeSite_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {z : Site d} :
-- imply
  removeSite z ω ≤ ω := by
-- proof
  apply StatMech.Percolation.cnp_removeSite_le ω z

/--
[cnp_axisRoutingPremise_of_clusterMeetsCorridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_axisRoutingPremise_of_clusterMeetsCorridor_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : cnp_ClusterMeetsCorridor ω x j L) :
-- imply
  craf_AxisRoutingPremise ω x j L := by
-- proof
  apply StatMech.Percolation.cnp_axisRoutingPremise_of_clusterMeetsCorridor ω x j L h

/--
[cnp_mouth_attachment_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_mouth_attachment_isPath_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {x : Site d}
  {m : ℕ}
  {pA : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk x (hrHD_rayPt j (m : ℤ))}
  {pB : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk (hrHD_rayPt j (m : ℤ)) (hrHD_rayPt j 1)}
-- given
  (hpA : pA.IsPath)
  (hpB : pB.IsPath)
  (hmeet : ∀ z, z ∈ pA.support → z ∈ pB.support → z = hrHD_rayPt j (m : ℤ)) :
-- imply
  (pA.append pB).IsPath := by
-- proof
  apply StatMech.Percolation.cnp_mouth_attachment_isPath ω j L x m pA pB hpA hpB hmeet

/--
[cnp_exists_simplePath_mouth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_exists_simplePath_mouth_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {x : Site d}
  {m : ℕ}
  {pA : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk x (hrHD_rayPt j (m : ℤ))}
  {pB : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk (hrHD_rayPt j (m : ℤ)) (hrHD_rayPt j 1)}
-- given
  (hpA : pA.IsPath)
  (hpB : pB.IsPath)
  (hmeet : ∀ z, z ∈ pA.support → z ∈ pB.support → z = hrHD_rayPt j (m : ℤ)) :
-- imply
  ∃ p : (openSubgraph d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω))).Walk x (hrHD_rayPt j 1), p.IsPath := by
-- proof
  apply StatMech.Percolation.cnp_exists_simplePath_mouth ω j L x m pA pB hpA hpB hmeet

/--
[cnp_clusterReachesRay_of_clusterMeetsCorridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_clusterReachesRay_of_clusterMeetsCorridor_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : cnp_ClusterMeetsCorridor ω x j L) :
-- imply
  lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j := by
-- proof
  apply StatMech.Percolation.cnp_clusterReachesRay_of_clusterMeetsCorridor ω x j L h

/--
[cnp_axisAssignment_of_clusterMeetsCorridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_axisAssignment_of_clusterMeetsCorridor_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : cnp_ClusterMeetsCorridor ω x j L) :
-- imply
  crr_AxisAssignment (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j := by
-- proof
  apply StatMech.Percolation.cnp_axisAssignment_of_clusterMeetsCorridor ω x j L h

/--
[cnp_burton_keane_uniqueness_of_boxReachesRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_burton_keane_uniqueness_of_boxReachesRay_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (hd : 3 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hres : ∀ n : ℕ, lma_BoxClusterReachesRay d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.cnp_burton_keane_uniqueness_of_boxReachesRay hd μ herg hfe bdry hbound hvol hdens hres

/--
[cnp_clusterMeetsCorridor_corridorCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_clusterMeetsCorridor_corridorCell_eq
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
  cnp_ClusterMeetsCorridor ω (hrHD_rayPt j (m : ℤ)) j L := by
-- proof
  apply StatMech.Percolation.cnp_clusterMeetsCorridor_corridorCell ω j L m hm1 hmL hinf

/--
[cnp_axisRoutingPremise_corridorCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_axisRoutingPremise_corridorCell_eq
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
  craf_AxisRoutingPremise ω (hrHD_rayPt j (m : ℤ)) j L := by
-- proof
  apply StatMech.Percolation.cnp_axisRoutingPremise_corridorCell ω j L m hm1 hmL hinf

/--
[cnp_clusterMeetsCorridor_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_clusterMeetsCorridor_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  cnp_ClusterMeetsCorridor ω (hrHD_rayPt j 1) j L := by
-- proof
  apply StatMech.Percolation.cnp_clusterMeetsCorridor_neighbour ω j L hinf

/--
[cnp_cut_someAxis_reach_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConnectProof.lean)
-/
@[path]
private lemma cnp_cut_someAxis_reach_of_infinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d (removeSite 0 ω) x y := by
-- proof
  apply StatMech.Percolation.cnp_cut_someAxis_reach_of_infinite ω x hinf n


-- created on 2026-10-23
