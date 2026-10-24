import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc14core
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc14_rayPt_mem_cluster_of_runsAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc14core.lean)
-/
@[path]
private lemma bc14_rayPt_mem_cluster_of_runsAlong_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : crr_ClusterRunsAlongAxis ω x j) :
-- imply
  hrHD_rayPt j 1 ∈ cluster d ω x := by
-- proof
  apply StatMech.Walls.bc14_rayPt_mem_cluster_of_runsAlong ω x j h

/--
[bc14_axes_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc14core.lean)
-/
@[path]
private lemma bc14_axes_distinct_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
  {j k : Fin d}
-- given
  (hne : cluster d ω x ≠ cluster d ω y)
  (hx : crr_ClusterRunsAlongAxis ω x j)
  (hy : crr_ClusterRunsAlongAxis ω y k) :
-- imply
  j ≠ k := by
-- proof
  apply StatMech.Walls.bc14_axes_distinct ω hne hx hy

/--
[bc14_boxClusterReachesRay_of_runsAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc14core.lean)
-/
@[path]
private lemma bc14_boxClusterReachesRay_of_runsAlong_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc14_BoxClusterRunsAlongAxis d n) :
-- imply
  lma_BoxClusterReachesRay d n := by
-- proof
  apply StatMech.Walls.bc14_boxClusterReachesRay_of_runsAlong h

/--
[bc14_bc13BoxClusterReachesRay_of_runsAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc14core.lean)
-/
@[path]
private lemma bc14_bc13BoxClusterReachesRay_of_runsAlong_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc14_BoxClusterRunsAlongAxis d n) :
-- imply
  bc13_BoxClusterReachesRay d n := by
-- proof
  apply StatMech.Walls.bc14_bc13BoxClusterReachesRay_of_runsAlong h

/--
[bc14_hroute_of_runsAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc14core.lean)
-/
@[path]
private lemma bc14_hroute_of_runsAlong_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hrun : ∀ n : ℕ, bc14_BoxClusterRunsAlongAxis d n) :
-- imply
  ∀ n : ℕ, 0 < μ (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc14_hroute_of_runsAlong μ hfe hrun

/--
[bc14_burton_keane_uniqueness_of_runsAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc14core.lean)
-/
@[path]
private lemma bc14_burton_keane_uniqueness_of_runsAlong_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hrun : ∀ n : ℕ, bc14_BoxClusterRunsAlongAxis d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc14_burton_keane_uniqueness_of_runsAlong μ herg hfe bdry hbound hvol hdens hrun

/--
[bc14_clusterRunsAlongAxis_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc14core.lean)
-/
@[path]
private lemma bc14_clusterRunsAlongAxis_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  ∃ j' : Fin d, crr_ClusterRunsAlongAxis ω (hrHD_rayPt j 1) j' := by
-- proof
  apply StatMech.Walls.bc14_clusterRunsAlongAxis_neighbour ω j hinf

/--
[bc14_boxClusterReachesRay_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc14core.lean)
-/
@[path]
private lemma bc14_boxClusterReachesRay_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hx1 : x₁ = hrHD_rayPt j₁ 1)
  (hx2 : x₂ = hrHD_rayPt j₂ 1)
  (hx3 : x₃ = hrHD_rayPt j₃ 1)
  (hi1 : (cluster d (removeSite 0 ω) x₁).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) x₂).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) x₃).Infinite) :
-- imply
  ∃ j₁' j₂' j₃' : Fin d, lma_ClusterReachesRay ω x₁ j₁' ∧ lma_ClusterReachesRay ω x₂ j₂' ∧ lma_ClusterReachesRay ω x₃ j₃' := by
-- proof
  apply StatMech.Walls.bc14_boxClusterReachesRay_nonvacuous ω x₁ x₂ x₃ j₁ j₂ j₃ hx1 hx2 hx3 hi1 hi2 hi3

/--
[bc14_runsAlong_arbitrary_omega_record](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc14core.lean)
-/
@[path]
private lemma bc14_runsAlong_arbitrary_omega_record_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d ω x).Infinite) :
-- imply
  ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y := by
-- proof
  apply StatMech.Walls.bc14_runsAlong_arbitrary_omega_record ω x hinf n


-- created on 2026-10-23
