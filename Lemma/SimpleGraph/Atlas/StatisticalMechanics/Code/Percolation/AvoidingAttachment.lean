import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.AvoidingAttachment
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[ava_support_mem_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_support_mem_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x z : Site d}
  {w : (openSubgraph d ω).Walk a x}
-- given
  (hz : z ∈ w.support) :
-- imply
  z ∈ cluster d ω x := by
-- proof
  apply StatMech.Percolation.ava_support_mem_cluster ω w hz

/--
[ava_origin_notMem_support_of_notMem_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_origin_notMem_support_of_notMem_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
  {w : (openSubgraph d ω).Walk a x}
-- given
  (h0 : (0 : Site d) ∉ cluster d ω x) :
-- imply
  (0 : Site d) ∉ w.support := by
-- proof
  apply StatMech.Percolation.ava_origin_notMem_support_of_notMem_cluster ω w h0

/--
[ava_removeSite_openSubgraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_removeSite_openSubgraph_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  openSubgraph d (removeSite 0 ω) ≤ openSubgraph d ω := by
-- proof
  apply StatMech.Percolation.ava_removeSite_openSubgraph_le ω

/--
[ava_origin_no_adj_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_origin_no_adj_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {y : Site d} :
-- imply
  ¬ (openSubgraph d (removeSite 0 ω)).Adj (0 : Site d) y := by
-- proof
  apply StatMech.Percolation.ava_origin_no_adj_removeSite ω y

/--
[ava_connected_origin_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_connected_origin_eq_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : Connected d (removeSite 0 ω) (0 : Site d) x) :
-- imply
  x = 0 := by
-- proof
  apply StatMech.Percolation.ava_connected_origin_eq ω h

/--
[ava_origin_notMem_cluster_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_origin_notMem_cluster_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hx : x ≠ 0) :
-- imply
  (0 : Site d) ∉ cluster d (removeSite 0 ω) x := by
-- proof
  apply StatMech.Percolation.ava_origin_notMem_cluster_removeSite ω hx

/--
[ava_avoiding_walk_of_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_avoiding_walk_of_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
-- given
  (hx : x ≠ 0)
  (hc : Connected d (removeSite 0 ω) a x) :
-- imply
  ∃ w : (openSubgraph d ω).Walk a x, (0 : Site d) ∉ w.support := by
-- proof
  apply StatMech.Percolation.ava_avoiding_walk_of_removeSite ω hx hc

/--
[ava_connected_of_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_connected_of_removeSite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
-- given
  (hc : Connected d (removeSite 0 ω) a x) :
-- imply
  Connected d ω a x := by
-- proof
  apply StatMech.Percolation.ava_connected_of_removeSite ω hc

/--
[ava_avoidingAttachment_of_removeSiteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_avoidingAttachment_of_removeSiteCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
-- given
  (hx : x ≠ 0)
  (hadj : (hypercubicLattice d).Adj 0 a)
  (hmemR : a ∈ cluster d (removeSite 0 ω) x)
  (hri : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  cla_AvoidingAttachment ω x := by
-- proof
  apply StatMech.Percolation.ava_avoidingAttachment_of_removeSiteCluster ω hx hadj hmemR hri

/--
[ava_avoidingAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_avoidingAttachment_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : ava_AvoidingRoutingResidue ω x) :
-- imply
  cla_AvoidingAttachment ω x := by
-- proof
  apply StatMech.Percolation.ava_avoidingAttachment ω x h

/--
[ava_clusterAttachment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_clusterAttachment_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : ava_AvoidingRoutingResidue ω x) :
-- imply
  bma_ClusterAttachment ω x := by
-- proof
  apply StatMech.Percolation.ava_clusterAttachment ω x h

/--
[ava_avoidingAttachment_of_notMemCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_avoidingAttachment_of_notMemCluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a x : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 a)
  (hmem : a ∈ cluster d ω x)
  (h0 : (0 : Site d) ∉ cluster d ω x)
  (hri : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  cla_AvoidingAttachment ω x := by
-- proof
  apply StatMech.Percolation.ava_avoidingAttachment_of_notMemCluster ω hadj hmem h0 hri

/--
[ava_avoidingRoutingResidue_of_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_avoidingRoutingResidue_of_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x)
  (hri : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  ava_AvoidingRoutingResidue ω x := by
-- proof
  apply StatMech.Percolation.ava_avoidingRoutingResidue_of_neighbour ω x hadj hri

/--
[ava_avoidingAttachment_of_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_avoidingAttachment_of_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x)
  (hri : (cluster d (removeSite 0 ω) x).Infinite) :
-- imply
  cla_AvoidingAttachment ω x := by
-- proof
  apply StatMech.Percolation.ava_avoidingAttachment_of_neighbour ω x hadj hri

/--
[ava_boxAvoidingAttachment_of_boxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_boxAvoidingAttachment_of_boxResidue_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : ava_BoxAvoidingRoutingResidue d n) :
-- imply
  cla_BoxAvoidingAttachment d n := by
-- proof
  apply StatMech.Percolation.ava_boxAvoidingAttachment_of_boxResidue h

/--
[ava_disjointRouting_of_boxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_disjointRouting_of_boxResidue_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : ava_BoxAvoidingRoutingResidue d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.ava_disjointRouting_of_boxResidue h

/--
[ava_three_residues_of_neighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AvoidingAttachment.lean)
-/
@[path]
private lemma ava_three_residues_of_neighbours_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 x₁ ∧ (hypercubicLattice d).Adj 0 x₂ ∧ (hypercubicLattice d).Adj 0 x₃)
  (hri : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) :
-- imply
  ava_AvoidingRoutingResidue ω x₁ ∧ ava_AvoidingRoutingResidue ω x₂ ∧ ava_AvoidingRoutingResidue ω x₃ := by
-- proof
  apply StatMech.Percolation.ava_three_residues_of_neighbours ω x₁ x₂ x₃ hadj hri


-- created on 2026-10-23
