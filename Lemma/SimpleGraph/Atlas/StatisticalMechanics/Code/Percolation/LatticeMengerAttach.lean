import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[lma_mem_corridorEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_mem_corridorEdges_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {t : ℕ}
-- given
  (ht : t < L) :
-- imply
  s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) ∈ lma_corridorEdges j L := by
-- proof
  apply StatMech.Percolation.lma_mem_corridorEdges ht

/--
[lma_corridorEdges_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_corridorEdges_zero_eq
  {d : ℕ}
  {j : Fin d} :
-- imply
  lma_corridorEdges j 0 = ∅ := by
-- proof
  apply StatMech.Percolation.lma_corridorEdges_zero j

/--
[lma_origin_notMem_corridorEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_origin_notMem_corridorEdges_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  ∀ e ∈ lma_corridorEdges j L, (0 : Site d) ∉ e := by
-- proof
  apply StatMech.Percolation.lma_origin_notMem_corridorEdges j L

/--
[lma_corridor_step_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_corridor_step_open_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {t : ℕ}
-- given
  (ht : t < L) :
-- imply
  IsOpenEdge d (removeSite 0 (forceOpenFinset (lma_corridorEdges j L) ω)) (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) := by
-- proof
  apply StatMech.Percolation.lma_corridor_step_open ω j L t ht

/--
[lma_corridor_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_corridor_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {m : ℕ}
-- given
  (hm : m ≤ L) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset (lma_corridorEdges j L) ω)) (hrHD_rayPt j 1) (hrHD_rayPt j ((m : ℤ) + 1)) := by
-- proof
  apply StatMech.Percolation.lma_corridor_connected ω j L m hm

/--
[lma_origin_notMem_corridorVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_origin_notMem_corridorVerts_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  (0 : Site d) ∉ lma_corridorVerts j L := by
-- proof
  apply StatMech.Percolation.lma_origin_notMem_corridorVerts j L

/--
[lma_corridorVerts_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_corridorVerts_disjoint_eq
  {d : ℕ}
  {j₁ j₂ : Fin d}
  {L : ℕ}
-- given
  (h : j₁ ≠ j₂) :
-- imply
  Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₂ L) := by
-- proof
  apply StatMech.Percolation.lma_corridorVerts_disjoint h L

/--
[lma_corridorEdges_endpoints_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_corridorEdges_endpoints_mem_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  ∀ e ∈ lma_corridorEdges j L, ∀ p, p ∈ e → p ∈ lma_corridorVerts j L := by
-- proof
  apply StatMech.Percolation.lma_corridorEdges_endpoints_mem j L

/--
[lma_removeSite_le_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_removeSite_le_forceOpen_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))} :
-- imply
  removeSite 0 ω ≤ removeSite 0 (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.lma_removeSite_le_forceOpen ω W

/--
[lma_clusterAttachment_of_reachesRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_clusterAttachment_of_reachesRay_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : lma_ClusterReachesRay ω x j) :
-- imply
  bma_ClusterAttachment ω x := by
-- proof
  apply StatMech.Percolation.lma_clusterAttachment_of_reachesRay ω x j h

/--
[lma_attachData_of_three_reachesRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_attachData_of_three_reachesRay_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h0 : lma_ClusterReachesRay ω x₁ j₁)
  (h1 : lma_ClusterReachesRay ω x₂ j₂)
  (h2 : lma_ClusterReachesRay ω x₃ j₃) :
-- imply
  tex_AttachData ω x₁ x₂ x₃ := by
-- proof
  apply StatMech.Percolation.lma_attachData_of_three_reachesRay ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h0 h1 h2

/--
[lma_threeClustersReachOrigin_of_three_reachesRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_threeClustersReachOrigin_of_three_reachesRay_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h0 : lma_ClusterReachesRay ω x₁ j₁)
  (h1 : lma_ClusterReachesRay ω x₂ j₂)
  (h2 : lma_ClusterReachesRay ω x₃ j₃) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.lma_threeClustersReachOrigin_of_three_reachesRay ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h0 h1 h2

/--
[lma_boxAttachData_of_reachesRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_boxAttachData_of_reachesRay_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : lma_BoxClusterReachesRay d n) :
-- imply
  tex_BoxAttachData d n := by
-- proof
  apply StatMech.Percolation.lma_boxAttachData_of_reachesRay h

/--
[lma_disjointRouting_of_reachesRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_disjointRouting_of_reachesRay_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : lma_BoxClusterReachesRay d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.lma_disjointRouting_of_reachesRay h

/--
[lma_clusterReachesRay_of_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_clusterReachesRay_of_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  lma_ClusterReachesRay ω (hrHD_rayPt j 1) j := by
-- proof
  apply StatMech.Percolation.lma_clusterReachesRay_of_neighbour ω j hinf

/--
[lma_attachData_of_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_attachData_of_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hcd12 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₂ 1))
  (hcd13 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
  (hcd23 : cluster d ω (hrHD_rayPt j₂ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
  (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite) :
-- imply
  tex_AttachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) := by
-- proof
  apply StatMech.Percolation.lma_attachData_of_neighbour_witnesses ω j₁ j₂ j₃ hcd12 hcd13 hcd23 hi1 hi2 hi3

/--
[lma_corridorVerts_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean)
-/
@[path]
private lemma lma_corridorVerts_nonempty_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  (lma_corridorVerts j L).Nonempty := by
-- proof
  apply StatMech.Percolation.lma_corridorVerts_nonempty j L


-- created on 2026-10-23
