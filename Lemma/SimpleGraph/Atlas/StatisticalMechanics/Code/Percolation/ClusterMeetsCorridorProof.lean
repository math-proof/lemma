import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.ClusterMeetsCorridorProof
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[cmc_clusterMeetsCorridor_of_runsAlongAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterMeetsCorridorProof.lean)
-/
@[path]
private lemma cmc_clusterMeetsCorridor_of_runsAlongAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : crr_ClusterRunsAlongAxis ω x j) :
-- imply
  cnp_ClusterMeetsCorridor ω x j L := by
-- proof
  apply StatMech.Percolation.cmc_clusterMeetsCorridor_of_runsAlongAxis ω x j L h

/--
[cmc_axisRoutingPremise_of_runsAlongAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterMeetsCorridorProof.lean)
-/
@[path]
private lemma cmc_axisRoutingPremise_of_runsAlongAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : crr_ClusterRunsAlongAxis ω x j) :
-- imply
  craf_AxisRoutingPremise ω x j L := by
-- proof
  apply StatMech.Percolation.cmc_axisRoutingPremise_of_runsAlongAxis ω x j L h

/--
[cmc_clusterReachesRay_of_runsAlongAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterMeetsCorridorProof.lean)
-/
@[path]
private lemma cmc_clusterReachesRay_of_runsAlongAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
  {L : ℕ}
-- given
  (h : crr_ClusterRunsAlongAxis ω x j) :
-- imply
  lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) x j := by
-- proof
  apply StatMech.Percolation.cmc_clusterReachesRay_of_runsAlongAxis ω x j L h

/--
[cmc_runsAlongAxis_entails_uncut_connection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterMeetsCorridorProof.lean)
-/
@[path]
private lemma cmc_runsAlongAxis_entails_uncut_connection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : crr_ClusterRunsAlongAxis ω x j) :
-- imply
  Connected d ω x (hrHD_rayPt j 1) := by
-- proof
  apply StatMech.Percolation.cmc_runsAlongAxis_entails_uncut_connection ω x j h

/--
[cmc_clusterMeetsCorridor_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterMeetsCorridorProof.lean)
-/
@[path]
private lemma cmc_clusterMeetsCorridor_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  cnp_ClusterMeetsCorridor ω (hrHD_rayPt j 1) j L := by
-- proof
  apply StatMech.Percolation.cmc_clusterMeetsCorridor_neighbour ω j L hinf

/--
[cmc_burton_keane_uniqueness_of_boxCandidates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterMeetsCorridorProof.lean)
-/
@[path]
private lemma cmc_burton_keane_uniqueness_of_boxCandidates_eq
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
  (hcand : ∀ n : ℕ, caa_BoxRunsAlongCandidates d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.cmc_burton_keane_uniqueness_of_boxCandidates hd μ herg hfe bdry hbound hvol hdens hcand

/--
[cmc_candidates_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterMeetsCorridorProof.lean)
-/
@[path]
private lemma cmc_candidates_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Fin 3 → Fin d}
-- given
  (ha : Function.Injective a)
  (hinf : ∀ i : Fin 3, (cluster d (removeSite 0 ω) (hrHD_rayPt (a i) 1)).Infinite) :
-- imply
  caa_RunsAlongCandidates ω (fun i => hrHD_rayPt (a i) 1) (fun i => ({a i} : Finset (Fin d))) := by
-- proof
  apply StatMech.Percolation.cmc_candidates_nonvacuous ω a ha hinf


-- created on 2026-10-23
