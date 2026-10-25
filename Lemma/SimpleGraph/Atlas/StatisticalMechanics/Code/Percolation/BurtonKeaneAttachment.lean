import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part4
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[bka_far_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_far_witness_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d ω w).Infinite) :
-- imply
  ∃ y, y ∉ box d n ∧ Connected d ω w y := by
-- proof
  apply StatMech.Percolation.bka_far_witness ω w hinf n

/--
[bka_exists_far_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_exists_far_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d ω w).Infinite) :
-- imply
  ∃ y ∈ cluster d ω w, y ∉ box d n := by
-- proof
  apply StatMech.Percolation.bka_exists_far_connected ω w hinf n

/--
[bka_isOpenEdge_survives](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_isOpenEdge_survives_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hopen : IsOpenEdge d ω x y)
  (h0 : (0 : Site d) ∉ s(x, y)) :
-- imply
  IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y := by
-- proof
  apply StatMech.Percolation.bka_isOpenEdge_survives ω G hopen h0

/--
[bka_axis_corridor_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_axis_corridor_step_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  Relation.ReflTransGen (CorridorStep (hrHD_corridorEdges j L)) (hrHD_rayPt j 1) (hrHD_rayPt j (L : ℤ)) := by
-- proof
  apply StatMech.Percolation.bka_axis_corridor_step j L hL

/--
[bka_three_independent_axis_neighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_three_independent_axis_neighbours_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
-- given
  (h12 : j₁ ≠ j₂)
  (h13 : j₁ ≠ j₃)
  (h23 : j₂ ≠ j₃) :
-- imply
  (hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₂ 1 ∧ hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₃ 1 ∧ hrHD_rayPt j₂ 1 ≠ hrHD_rayPt j₃ 1) ∧ ((hypercubicLattice d).Adj 0 (hrHD_rayPt j₁ 1) ∧ (hypercubicLattice d).Adj 0 (hrHD_rayPt j₂ 1) ∧ (hypercubicLattice d).Adj 0 (hrHD_rayPt j₃ 1)) ∧ (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₂ t) ∧ (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₃ t) ∧ (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₂ s ≠ hrHD_rayPt j₃ t) := by
-- proof
  apply StatMech.Percolation.bka_three_independent_axis_neighbours h12 h13 h23

/--
[bka_forceOpenFinset_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_forceOpenFinset_empty_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
-- proof
  apply StatMech.Percolation.bka_forceOpenFinset_empty ω

/--
[bka_corridor_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_corridor_refl_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))}
  {a : Site d} :
-- imply
  Relation.ReflTransGen (CorridorStep G) a a := by
-- proof
  apply StatMech.Percolation.bka_corridor_refl G a

/--
[bka_distinct_clusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_distinct_clusters_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bka_MergeFree ω) :
-- imply
  bcc_distinct_clusters_residue ω := by
-- proof
  apply StatMech.Percolation.bka_distinct_clusters ω h

/--
[bka_disjointRouting_of_mergeFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_disjointRouting_of_mergeFree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bka_MergeFree ω) :
-- imply
  DisjointCorridorRouting ω := by
-- proof
  apply StatMech.Percolation.bka_disjointRouting_of_mergeFree ω h

/--
[bka_routing_of_mergeFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_routing_of_mergeFree_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hmf : ∀ ω ∈ threeMeetBox d n, bka_MergeFree ω) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.bka_routing_of_mergeFree n hmf

/--
[bka_rhoOpenEdge_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_rhoOpenEdge_decompose_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hadj : (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v) :
-- imply
  (hypercubicLattice d).Adj u v ∧ (0 : Site d) ∉ s(u, v) ∧ (IsOpenEdge d ω u v ∨ s(u, v) ∈ G) := by
-- proof
  apply StatMech.Percolation.bka_rhoOpenEdge_decompose ω G hadj

/--
[bka_no_crossing_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_no_crossing_edge_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
  {u v : Site d}
-- given
  (hne : cluster d ω x ≠ cluster d ω y)
  (hu : u ∈ cluster d ω x)
  (hv : v ∈ cluster d ω y)
  (hedge : IsOpenEdge d ω u v) :
-- imply
  False := by
-- proof
  apply StatMech.Percolation.bka_no_crossing_edge ω hne hu hv hedge

/--
[bka_region_rhoAdjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_region_rhoAdjClosed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {R : Set (Site d)}
-- given
  (homega : ∀ u v, u ∈ R → IsOpenEdge d ω u v → v ∈ R)
  (hG : ∀ u v, u ∈ R → s(u, v) ∈ G → v ∈ R) :
-- imply
  ∀ u v, u ∈ R → (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ R := by
-- proof
  apply StatMech.Percolation.bka_region_rhoAdjClosed ω G R homega hG

/--
[bka_distinct_clusters_of_clusterRespecting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_distinct_clusters_of_clusterRespecting_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bka_ClusterRespectingRouting ω) :
-- imply
  DisjointCorridorRouting ω := by
-- proof
  apply StatMech.Percolation.bka_distinct_clusters_of_clusterRespecting ω h

/--
[bka_disjointRouting_of_corridorConfinement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_disjointRouting_of_corridorConfinement_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bka_CorridorConfinement ω) :
-- imply
  DisjointCorridorRouting ω := by
-- proof
  apply StatMech.Percolation.bka_disjointRouting_of_corridorConfinement ω h

/--
[bka_distinct_clusters_of_corridorConfinement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_distinct_clusters_of_corridorConfinement_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bka_CorridorConfinement ω) :
-- imply
  bcc_distinct_clusters_residue ω := by
-- proof
  apply StatMech.Percolation.bka_distinct_clusters_of_corridorConfinement ω h

/--
[bka_residue_iff_corridorConfinement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean)
-/
@[path]
private lemma bka_residue_iff_corridorConfinement_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  bcc_distinct_clusters_residue ω ↔ bka_CorridorConfinement ω := by
-- proof
  apply StatMech.Percolation.bka_residue_iff_corridorConfinement ω


-- created on 2026-10-23
