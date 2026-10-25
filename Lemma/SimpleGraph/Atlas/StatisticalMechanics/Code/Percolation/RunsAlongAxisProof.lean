import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.RunsAlongAxisProof
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[rap_runsAlongAxis_ray_open_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RunsAlongAxisProof.lean)
-/
@[path]
private lemma rap_runsAlongAxis_ray_open_edges_eq
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
  apply StatMech.Percolation.rap_runsAlongAxis_ray_open_edges ω j L ht

/--
[rap_runsAlongAxis_ray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RunsAlongAxisProof.lean)
-/
@[path]
private lemma rap_runsAlongAxis_ray_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) (hrHD_rayPt j 1)).Infinite) :
-- imply
  (∀ t : ℕ, t < L → forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true) ∧ crr_ClusterRunsAlongAxis (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1) j := by
-- proof
  apply StatMech.Percolation.rap_runsAlongAxis_ray ω j L hinf

/--
[rap_far_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RunsAlongAxisProof.lean)
-/
@[path]
private lemma rap_far_reach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ} :
-- imply
  Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) (hrHD_rayPt j 1) (hrHD_rayPt j ((L : ℤ) + 1)) := by
-- proof
  apply StatMech.Percolation.rap_far_reach ω j L

/--
[rap_clusterReachesRay_ray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RunsAlongAxisProof.lean)
-/
@[path]
private lemma rap_clusterReachesRay_ray_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) (hrHD_rayPt j 1)).Infinite) :
-- imply
  lma_ClusterReachesRay (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1) j := by
-- proof
  apply StatMech.Percolation.rap_clusterReachesRay_ray ω j L hinf

/--
[rap_clusterMeetsCorridor_ray](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RunsAlongAxisProof.lean)
-/
@[path]
private lemma rap_clusterMeetsCorridor_ray_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L L' : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) (hrHD_rayPt j 1)).Infinite) :
-- imply
  cnp_ClusterMeetsCorridor (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1) j L' := by
-- proof
  apply StatMech.Percolation.rap_clusterMeetsCorridor_ray ω j L L' hinf

/--
[rap_burton_keane_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RunsAlongAxisProof.lean)
-/
@[path]
private lemma rap_burton_keane_uniqueness_eq
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
  apply StatMech.Percolation.rap_burton_keane_uniqueness hd μ herg hfe bdry hbound hvol hdens hcand

/--
[rap_ray_open_edge_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RunsAlongAxisProof.lean)
-/
@[path]
private lemma rap_ray_open_edge_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω s(hrHD_rayPt j (((0 : ℕ) : ℤ) + 1), hrHD_rayPt j (((0 : ℕ) : ℤ) + 2)) = true := by
-- proof
  apply StatMech.Percolation.rap_ray_open_edge_nonvacuous ω j L hL

/--
[rap_candidates_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RunsAlongAxisProof.lean)
-/
@[path]
private lemma rap_candidates_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Fin 3 → Fin d}
-- given
  (ha : Function.Injective a)
  (hinf : ∀ i : Fin 3, (cluster d (removeSite 0 ω) (hrHD_rayPt (a i) 1)).Infinite) :
-- imply
  caa_RunsAlongCandidates ω (fun i => hrHD_rayPt (a i) 1) (fun i => ({a i} : Finset (Fin d))) := by
-- proof
  apply StatMech.Percolation.rap_candidates_neighbour ω a ha hinf

/--
[rap_runsAlongAxis_entails_near_connection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RunsAlongAxisProof.lean)
-/
@[path]
private lemma rap_runsAlongAxis_entails_near_connection_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hinf : (cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω)) (hrHD_rayPt j 1)).Infinite) :
-- imply
  Connected d (forceOpenFinset (hrHD_corridorEdges j (L + 1)) ω) (hrHD_rayPt j 1) (hrHD_rayPt j 1) := by
-- proof
  apply StatMech.Percolation.rap_runsAlongAxis_entails_near_connection ω j L hinf


-- created on 2026-10-23
