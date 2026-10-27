import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation StatMech.Percolation.DisjointPaths


/--
[mng_cluster_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerRouting.lean)
-/
@[path]
private lemma mng_cluster_adjClosed_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {w : Site d}
  {u v : Site d}
-- given
  (hu : u ∈ cluster d ϱ w)
  (hadj : (openSubgraph d ϱ).Adj u v) :
-- imply
  v ∈ cluster d ϱ w := by
-- proof
  apply StatMech.Percolation.DisjointPaths.mng_cluster_adjClosed ϱ w hu hadj

/--
[mng_corridor_mem_destCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerRouting.lean)
-/
@[path]
private lemma mng_corridor_mem_destCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {a w : Site d}
-- given
  (hc : Relation.ReflTransGen (CorridorStep G) a w) :
-- imply
  a ∈ cluster d (removeSite 0 (forceOpenFinset G ω)) w := by
-- proof
  apply StatMech.Percolation.DisjointPaths.mng_corridor_mem_destCluster ω G hc

/--
[mng_disjoint_of_cluster_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerRouting.lean)
-/
@[path]
private lemma mng_disjoint_of_cluster_ne_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {w₁ w₂ : Site d}
-- given
  (h : cluster d ϱ w₁ ≠ cluster d ϱ w₂) :
-- imply
  Disjoint (cluster d ϱ w₁) (cluster d ϱ w₂) := by
-- proof
  apply StatMech.Percolation.DisjointPaths.mng_disjoint_of_cluster_ne ϱ w₁ w₂ h

/--
[mng_disjointRouting_of_mengerCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerRouting.lean)
-/
@[path]
private lemma mng_disjointRouting_of_mengerCore_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : MengerCore ω) :
-- imply
  DisjointCorridorRouting ω := by
-- proof
  apply StatMech.Percolation.DisjointPaths.mng_disjointRouting_of_mengerCore ω h

/--
[mng_forceOpenFinset_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerRouting.lean)
-/
@[path]
private lemma mng_forceOpenFinset_empty_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
-- proof
  apply StatMech.Percolation.DisjointPaths.mng_forceOpenFinset_empty ω

/--
[mng_mengerCore_of_neighborClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerRouting.lean)
-/
@[path]
private lemma mng_mengerCore_of_neighborClusters_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hinf : (cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧ (cluster d (removeSite 0 ω) a₃).Infinite)
  (hdist : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧ cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧ cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
-- imply
  MengerCore ω := by
-- proof
  apply StatMech.Percolation.DisjointPaths.mng_mengerCore_of_neighborClusters ω a₁ a₂ a₃ hne hadj hinf hdist

/--
[mng_disjointRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerRouting.lean)
-/
@[path]
private lemma mng_disjointRouting_eq
  {d : ℕ}
  {d n : ℕ}
-- given
  (hcov : MengerRoutingCover d n) :
-- imply
  ∀ ω ∈ threeMeetBox d n, DisjointCorridorRouting ω := by
-- proof
  apply StatMech.Percolation.DisjointPaths.mng_disjointRouting d n hcov

/--
[mng_corridorCover_of_mengerCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerRouting.lean)
-/
@[path]
private lemma mng_corridorCover_of_mengerCover_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hcov : MengerRoutingCover d n) :
-- imply
  threeMeetBox d n ⊆ ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))), CorridorWorks a₁ a₂ a₃ G := by
-- proof
  apply StatMech.Percolation.DisjointPaths.mng_corridorCover_of_mengerCover hcov

/--
[mng_burton_keane_uniqueness_mengerCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerRouting.lean)
-/
@[path]
private lemma mng_burton_keane_uniqueness_mengerCover_eq
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
  (hcov : ∀ n : ℕ, MengerRoutingCover d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.DisjointPaths.mng_burton_keane_uniqueness_mengerCover μ herg hfe bdry hbound hvol hdens hcov


-- created on 2026-10-23
