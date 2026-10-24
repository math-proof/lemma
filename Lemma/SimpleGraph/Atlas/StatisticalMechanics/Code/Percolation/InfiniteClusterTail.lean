import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.InfiniteClusterTail
open Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[infiniteCluster_component_after_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean)
-/
@[path]
private lemma infiniteCluster_component_after_finset_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {K : Finset (Site d)}
-- given
  (hinf : (cluster d omega x).Infinite) :
-- imply
  ∃ D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K), D.supp.Infinite := by
-- proof
  apply StatMech.Percolation.infiniteCluster_component_after_finset omega x hinf K

/--
[tailComponentSites_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean)
-/
@[path]
private lemma tailComponentSites_infinite_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {K : Finset (Site d)}
  {D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)}
-- given
  (hD : D.supp.Infinite) :
-- imply
  (tailComponentSites omega x K D).Infinite := by
-- proof
  apply StatMech.Percolation.tailComponentSites_infinite omega x K D hD

/--
[tailComponentSites_subset_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean)
-/
@[path]
private lemma tailComponentSites_subset_cluster_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {K : Finset (Site d)}
  {D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)} :
-- imply
  tailComponentSites omega x K D ⊆ cluster d omega x := by
-- proof
  apply StatMech.Percolation.tailComponentSites_subset_cluster omega x K D

/--
[tailComponentSites_connected_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean)
-/
@[path]
private lemma tailComponentSites_connected_outside_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {K : Finset (Site d)}
  {D : (tailClusterGraph omega x).ComponentCompl (tailClusterCut omega x K)} :
-- imply
  ∀ u ∈ tailComponentSites omega x K D, ∀ v ∈ tailComponentSites omega x K D, ∃ (hu : u ∉ (K : Set (Site d))) (hv : v ∉ (K : Set (Site d))), ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
-- proof
  apply StatMech.Percolation.tailComponentSites_connected_outside omega x K D

/--
[infiniteCluster_has_tail_outside_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean)
-/
@[path]
private lemma infiniteCluster_has_tail_outside_finset_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {K : Finset (Site d)}
-- given
  (hinf : (cluster d omega x).Infinite) :
-- imply
  ∃ T : Set (Site d), T.Infinite ∧ T ⊆ cluster d omega x ∧ (∀ u ∈ T, ∀ v ∈ T, ∃ (hu : u ∉ (K : Set (Site d))) (hv : v ∉ (K : Set (Site d))), ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩) := by
-- proof
  apply StatMech.Percolation.infiniteCluster_has_tail_outside_finset omega x hinf K

/--
[infiniteCluster_has_open_exit_to_infinite_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean)
-/
@[path]
private lemma infiniteCluster_has_open_exit_to_infinite_tail_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {K : Finset (Site d)}
-- given
  (hinf : (cluster d omega x).Infinite)
  (hxK : x ∈ K) :
-- imply
  ∃ u v : Site d, ∃ T : Set (Site d), u ∈ K ∧ v ∉ K ∧ (openSubgraph d omega).Adj u v ∧ v ∈ T ∧ T.Infinite ∧ T ⊆ cluster d omega x ∧ (∀ a ∈ T, ∀ b ∈ T, ∃ (ha : a ∉ (K : Set (Site d))) (hb : b ∉ (K : Set (Site d))), ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable ⟨a, ha⟩ ⟨b, hb⟩) := by
-- proof
  apply StatMech.Percolation.infiniteCluster_has_open_exit_to_infinite_tail omega x hinf K hxK

/--
[disjoint_clusters_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean)
-/
@[path]
private lemma disjoint_clusters_of_ne_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hne : cluster d omega x ≠ cluster d omega y) :
-- imply
  Disjoint (cluster d omega x) (cluster d omega y) := by
-- proof
  apply StatMech.Percolation.disjoint_clusters_of_ne omega hne

/--
[threeInfiniteClusters_have_disjoint_tails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean)
-/
@[path]
private lemma threeInfiniteClusters_have_disjoint_tails_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {K : Finset (Site d)}
  {x1 x2 x3 : Site d}
-- given
  (hx1 : x1 ∈ K)
  (hx2 : x2 ∈ K)
  (hx3 : x3 ∈ K)
  (hi1 : (cluster d omega x1).Infinite)
  (hi2 : (cluster d omega x2).Infinite)
  (hi3 : (cluster d omega x3).Infinite)
  (hne12 : cluster d omega x1 ≠ cluster d omega x2)
  (hne13 : cluster d omega x1 ≠ cluster d omega x3)
  (hne23 : cluster d omega x2 ≠ cluster d omega x3) :
-- imply
  ∃ D1 : InfiniteClusterTailData omega K x1, ∃ D2 : InfiniteClusterTailData omega K x2, ∃ D3 : InfiniteClusterTailData omega K x3, Disjoint D1.tail D2.tail ∧ Disjoint D1.tail D3.tail ∧ Disjoint D2.tail D3.tail := by
-- proof
  apply StatMech.Percolation.threeInfiniteClusters_have_disjoint_tails omega K x1 x2 x3 hx1 hx2 hx3 hi1 hi2 hi3 hne12 hne13 hne23


-- created on 2026-10-23
