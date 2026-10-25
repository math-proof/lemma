import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc13core
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc13_hroute_of_clusterReachesRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc13core.lean)
-/
@[path]
private lemma bc13_hroute_of_clusterReachesRay_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hreach : ∀ n : ℕ, bc13_BoxClusterReachesRay d n) :
-- imply
  ∀ n : ℕ, 0 < μ (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc13_hroute_of_clusterReachesRay μ hfe hreach

/--
[bc13_htrif_of_clusterReachesRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc13core.lean)
-/
@[path]
private lemma bc13_htrif_of_clusterReachesRay_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hreach : ∀ n : ℕ, bc13_BoxClusterReachesRay d n) :
-- imply
  0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsTrifurcation d ω 0} := by
-- proof
  apply StatMech.Walls.bc13_htrif_of_clusterReachesRay μ hfe hreach

/--
[bc13_burton_keane_uniqueness_of_clusterReachesRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc13core.lean)
-/
@[path]
private lemma bc13_burton_keane_uniqueness_of_clusterReachesRay_eq
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
  (hreach : ∀ n : ℕ, bc13_BoxClusterReachesRay d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc13_burton_keane_uniqueness_of_clusterReachesRay μ herg hfe bdry hbound hvol hdens hreach

/--
[bc13_clusterReachesRay_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc13core.lean)
-/
@[path]
private lemma bc13_clusterReachesRay_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  lma_ClusterReachesRay ω (hrHD_rayPt j 1) j := by
-- proof
  apply StatMech.Walls.bc13_clusterReachesRay_neighbour ω j hinf

/--
[bc13_boxClusterReachesRay_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc13core.lean)
-/
@[path]
private lemma bc13_boxClusterReachesRay_nonvacuous_eq
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
  apply StatMech.Walls.bc13_boxClusterReachesRay_nonvacuous ω x₁ x₂ x₃ j₁ j₂ j₃ hx1 hx2 hx3 hi1 hi2 hi3

/--
[bc13_clusterReachesRay_arbitrary_omega_record](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc13core.lean)
-/
@[path]
private lemma bc13_clusterReachesRay_arbitrary_omega_record_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d ω x).Infinite) :
-- imply
  ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y := by
-- proof
  apply StatMech.Walls.bc13_clusterReachesRay_arbitrary_omega_record ω x hinf n


-- created on 2026-10-23
