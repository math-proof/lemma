import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc9nbrcutcluster
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech StatMech.Walls


/--
[bc9nbr_adj_survives_origin_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9nbrcutcluster.lean)
-/
@[path]
private lemma bc9nbr_adj_survives_origin_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u w : Site d}
-- given
  (hu : u ≠ 0)
  (hw : w ≠ 0)
  (hadj : (openSubgraph d ω).Adj u w) :
-- imply
  (openSubgraph d (removeSite 0 ω)).Adj u w := by
-- proof
  apply StatMech.Walls.bc9nbr_adj_survives_origin_cut ω hu hw hadj

/--
[bc9nbr_adj_dies_origin_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9nbrcutcluster.lean)
-/
@[path]
private lemma bc9nbr_adj_dies_origin_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u w : Site d}
-- given
  (h0 : (0 : Site d) ∈ s(u, w)) :
-- imply
  ¬ (openSubgraph d (removeSite 0 ω)).Adj u w := by
-- proof
  apply StatMech.Walls.bc9nbr_adj_dies_origin_cut ω h0

/--
[bc9nbr_avoiding_walk_survives_origin_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9nbrcutcluster.lean)
-/
@[path]
private lemma bc9nbr_avoiding_walk_survives_origin_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u w : Site d}
  {p : (openSubgraph d ω).Walk u w}
-- given
  (hp : (0 : Site d) ∉ p.support) :
-- imply
  Connected d (removeSite 0 ω) u w := by
-- proof
  apply StatMech.Walls.bc9nbr_avoiding_walk_survives_origin_cut ω p hp

/--
[bc9nbr_origin_neighbour_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9nbrcutcluster.lean)
-/
@[path]
private lemma bc9nbr_origin_neighbour_of_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (hy0 : y ≠ 0)
  (hconn : Connected d ω 0 y) :
-- imply
  ∃ n, (openSubgraph d ω).Adj 0 n ∧ ∃ r : (openSubgraph d ω).Walk n y, (0 : Site d) ∉ r.support := by
-- proof
  apply StatMech.Walls.bc9nbr_origin_neighbour_of_connected ω hy0 hconn

/--
[bc9nbr_mem_neighbour_cutCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9nbrcutcluster.lean)
-/
@[path]
private lemma bc9nbr_mem_neighbour_cutCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (hy0 : y ≠ 0)
  (hconn : Connected d ω 0 y) :
-- imply
  ∃ n, (openSubgraph d ω).Adj 0 n ∧ y ∈ cluster d (removeSite 0 ω) n := by
-- proof
  apply StatMech.Walls.bc9nbr_mem_neighbour_cutCluster ω hy0 hconn

/--
[bc9nbr_mem_neighbour_cutCluster'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9nbrcutcluster.lean)
-/
@[path]
private lemma bc9nbr_mem_neighbour_cutCluster'_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (hy0 : y ≠ 0)
  (hconn : Connected d ω y 0) :
-- imply
  ∃ n, (openSubgraph d ω).Adj 0 n ∧ y ∈ cluster d (removeSite 0 ω) n := by
-- proof
  apply StatMech.Walls.bc9nbr_mem_neighbour_cutCluster' ω hy0 hconn

/--
[bc9nbr_mem_neighbour_cutCluster_strong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9nbrcutcluster.lean)
-/
@[path]
private lemma bc9nbr_mem_neighbour_cutCluster_strong_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (hy0 : y ≠ 0)
  (hconn : Connected d ω 0 y) :
-- imply
  ∃ n, (openSubgraph d ω).Adj 0 n ∧ Connected d (removeSite 0 ω) n y ∧ y ∈ cluster d (removeSite 0 ω) n := by
-- proof
  apply StatMech.Walls.bc9nbr_mem_neighbour_cutCluster_strong ω hy0 hconn

/--
[bc9nbr_mem_neighbour_cutCluster_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc9nbrcutcluster.lean)
-/
@[path]
private lemma bc9nbr_mem_neighbour_cutCluster_of_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d}
-- given
  (hy0 : y ≠ 0)
  (hadj : (openSubgraph d ω).Adj 0 y) :
-- imply
  ∃ n, (openSubgraph d ω).Adj 0 n ∧ y ∈ cluster d (removeSite 0 ω) n := by
-- proof
  apply StatMech.Walls.bc9nbr_mem_neighbour_cutCluster_of_adj ω hy0 hadj


-- created on 2026-10-23
