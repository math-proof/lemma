import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.CorridorSidesFromClusters
open StatMech StatMech.Percolation


/--
[csc_cluster_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorSidesFromClusters.lean)
-/
@[path]
private lemma csc_cluster_adjClosed_eq
  {d : ℕ}
  {ω' : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  ∀ u v, u ∈ cluster d ω' x → (openSubgraph d ω').Adj u v → v ∈ cluster d ω' x := by
-- proof
  apply StatMech.Percolation.csc_cluster_adjClosed ω' x

/--
[csc_clusters_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorSidesFromClusters.lean)
-/
@[path]
private lemma csc_clusters_disjoint_eq
  {d : ℕ}
  {ω' : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : ¬ Connected d ω' x y) :
-- imply
  Disjoint (cluster d ω' x) (cluster d ω' y) := by
-- proof
  apply StatMech.Percolation.csc_clusters_disjoint ω' h

/--
[csc_disjointCorridorRouting_of_distinctClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorSidesFromClusters.lean)
-/
@[path]
private lemma csc_disjointCorridorRouting_of_distinctClusters_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : csc_DistinctClusterCorridors ω) :
-- imply
  DisjointCorridorRouting ω := by
-- proof
  apply StatMech.Percolation.csc_disjointCorridorRouting_of_distinctClusters ω h

/--
[csc_corridorCover_of_distinctClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorSidesFromClusters.lean)
-/
@[path]
private lemma csc_corridorCover_of_distinctClusters_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : ∀ ω ∈ threeMeetBox d n, csc_DistinctClusterCorridors ω) :
-- imply
  threeMeetBox d n ⊆ ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))), CorridorWorks a₁ a₂ a₃ G := by
-- proof
  apply StatMech.Percolation.csc_corridorCover_of_distinctClusters h


-- created on 2026-10-23
