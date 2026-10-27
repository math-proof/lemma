import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc7offboxsubsetcluster
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc7_clusterWithin_subset_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxsubsetcluster.lean)
-/
@[path]
private lemma bc7_clusterWithin_subset_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {o : Site d} :
-- imply
  clusterWithin d ω S o ⊆ cluster d ω o := by
-- proof
  apply StatMech.Walls.bc7_clusterWithin_subset_cluster ω S o

/--
[bc7_offBoxCluster_subset_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxsubsetcluster.lean)
-/
@[path]
private lemma bc7_offBoxCluster_subset_cluster_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  bc6_offBoxCluster N a R ω ⊆ cluster d (removeSite 0 ω) (hrHD_rayPt a (R : ℤ)) := by
-- proof
  apply StatMech.Walls.bc7_offBoxCluster_subset_cluster ω

/--
[bc7_offBoxCluster_connected_farEnd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxsubsetcluster.lean)
-/
@[path]
private lemma bc7_offBoxCluster_connected_farEnd_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hx : x ∈ bc6_offBoxCluster N a R ω) :
-- imply
  Connected d (removeSite 0 ω) (hrHD_rayPt a (R : ℤ)) x := by
-- proof
  apply StatMech.Walls.bc7_offBoxCluster_connected_farEnd hx

/--
[bc7_offBoxCluster_subset_cluster_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxsubsetcluster.lean)
-/
@[path]
private lemma bc7_offBoxCluster_subset_cluster_self_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hx : x ∈ bc6_offBoxCluster N a R ω) :
-- imply
  bc6_offBoxCluster N a R ω ⊆ cluster d (removeSite 0 ω) x := by
-- proof
  apply StatMech.Walls.bc7_offBoxCluster_subset_cluster_self hx


-- created on 2026-10-23
