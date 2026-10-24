import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.MengerCorridors
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[mco_mergeFree_of_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_mergeFree_of_reach_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ x₁ x₂ x₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hconn : Connected d (removeSite 0 ω) a₁ x₁ ∧ Connected d (removeSite 0 ω) a₂ x₂ ∧ Connected d (removeSite 0 ω) a₃ x₃)
  (hinf : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite)
  (hdist : cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧ cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧ cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃) :
-- imply
  bka_MergeFree ω := by
-- proof
  apply StatMech.Percolation.mco_mergeFree_of_reach ω a₁ a₂ a₃ x₁ x₂ x₃ hadj hconn hinf hdist

/--
[mco_mergeFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_mergeFree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : mco_ThreeClustersReachOrigin ω) :
-- imply
  bka_MergeFree ω := by
-- proof
  apply StatMech.Percolation.mco_mergeFree ω h

/--
[mco_distinct_clusters_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_distinct_clusters_residue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : mco_ThreeClustersReachOrigin ω) :
-- imply
  bcc_distinct_clusters_residue ω := by
-- proof
  apply StatMech.Percolation.mco_distinct_clusters_residue ω h

/--
[mco_disjointRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_disjointRouting_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : mco_ThreeClustersReachOrigin ω) :
-- imply
  DisjointPaths.DisjointCorridorRouting ω := by
-- proof
  apply StatMech.Percolation.mco_disjointRouting ω h

/--
[mco_routing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_routing_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hreach : ∀ ω ∈ threeMeetBox d n, mco_ThreeClustersReachOrigin ω) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.mco_routing n hreach

/--
[mco_rayPt_one_mem_corridorVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_rayPt_one_mem_corridorVerts_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  hrHD_rayPt j 1 ∈ mco_corridorVerts j L := by
-- proof
  apply StatMech.Percolation.mco_rayPt_one_mem_corridorVerts j L hL

/--
[mco_origin_notMem_corridorVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_origin_notMem_corridorVerts_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  (0 : Site d) ∉ mco_corridorVerts j L := by
-- proof
  apply StatMech.Percolation.mco_origin_notMem_corridorVerts j L

/--
[mco_corridorVerts_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_corridorVerts_disjoint_eq
  {d : ℕ}
  {j₁ j₂ : Fin d}
  {L : ℕ}
-- given
  (h : j₁ ≠ j₂) :
-- imply
  Disjoint (mco_corridorVerts j₁ L) (mco_corridorVerts j₂ L) := by
-- proof
  apply StatMech.Percolation.mco_corridorVerts_disjoint h L

/--
[mco_corridorVert_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_corridorVert_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {m : ℕ}
-- given
  (hm1 : 1 ≤ m)
  (hmL : m ≤ L) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω)) (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) := by
-- proof
  apply StatMech.Percolation.mco_corridorVert_connected ω j L m hm1 hmL

/--
[mco_corridorVerts_subset_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_corridorVerts_subset_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ} :
-- imply
  mco_corridorVerts j L ⊆ cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω)) (hrHD_rayPt j 1) := by
-- proof
  apply StatMech.Percolation.mco_corridorVerts_subset_cluster ω j L

/--
[mco_three_disjoint_corridors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_three_disjoint_corridors_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L : ℕ}
-- given
  (h12 : j₁ ≠ j₂)
  (h13 : j₁ ≠ j₃)
  (h23 : j₂ ≠ j₃)
  (hL : 1 ≤ L) :
-- imply
  ∃ C₁ C₂ C₃ : Set (Site d), (hrHD_rayPt j₁ 1 ∈ C₁ ∧ hrHD_rayPt j₂ 1 ∈ C₂ ∧ hrHD_rayPt j₃ 1 ∈ C₃) ∧ ((hypercubicLattice d).Adj 0 (hrHD_rayPt j₁ 1) ∧ (hypercubicLattice d).Adj 0 (hrHD_rayPt j₂ 1) ∧ (hypercubicLattice d).Adj 0 (hrHD_rayPt j₃ 1)) ∧ ((0 : Site d) ∉ C₁ ∧ (0 : Site d) ∉ C₂ ∧ (0 : Site d) ∉ C₃) ∧ (Disjoint C₁ C₂ ∧ Disjoint C₁ C₃ ∧ Disjoint C₂ C₃) ∧ ((∀ y ∈ C₁, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₁ L) ω)) (hrHD_rayPt j₁ 1) y) ∧ (∀ y ∈ C₂, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₂ L) ω)) (hrHD_rayPt j₂ 1) y) ∧ (∀ y ∈ C₃, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₃ L) ω)) (hrHD_rayPt j₃ 1) y)) := by
-- proof
  apply StatMech.Percolation.mco_three_disjoint_corridors ω h12 h13 h23 L hL

/--
[mco_corridors_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_corridors_nonvacuous_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  (mco_corridorVerts j L).Nonempty := by
-- proof
  apply StatMech.Percolation.mco_corridors_nonvacuous j L hL

/--
[mco_exists_three_disjoint_corridors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean)
-/
@[path]
private lemma mco_exists_three_disjoint_corridors_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
-- given
  (hd : 3 ≤ d)
  (hL : 1 ≤ L) :
-- imply
  ∃ (j₁ j₂ j₃ : Fin d) (C₁ C₂ C₃ : Set (Site d)), (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧ (hrHD_rayPt j₁ 1 ∈ C₁ ∧ hrHD_rayPt j₂ 1 ∈ C₂ ∧ hrHD_rayPt j₃ 1 ∈ C₃) ∧ ((hypercubicLattice d).Adj 0 (hrHD_rayPt j₁ 1) ∧ (hypercubicLattice d).Adj 0 (hrHD_rayPt j₂ 1) ∧ (hypercubicLattice d).Adj 0 (hrHD_rayPt j₃ 1)) ∧ ((0 : Site d) ∉ C₁ ∧ (0 : Site d) ∉ C₂ ∧ (0 : Site d) ∉ C₃) ∧ (Disjoint C₁ C₂ ∧ Disjoint C₁ C₃ ∧ Disjoint C₂ C₃) ∧ ((∀ y ∈ C₁, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₁ L) ω)) (hrHD_rayPt j₁ 1) y) ∧ (∀ y ∈ C₂, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₂ L) ω)) (hrHD_rayPt j₂ 1) y) ∧ (∀ y ∈ C₃, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₃ L) ω)) (hrHD_rayPt j₃ 1) y)) := by
-- proof
  apply StatMech.Percolation.mco_exists_three_disjoint_corridors ω hd L hL


-- created on 2026-10-23
