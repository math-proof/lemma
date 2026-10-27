import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc3_core.Part3
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc3_mem_clusterNbhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_mem_clusterNbhd_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
  {x : Site d} :
-- imply
  x ∈ bc3_clusterNbhd ω j L ↔ ∃ t : ℕ, (1 ≤ t ∧ t ≤ L) ∧ x ∈ cluster d (removeSite 0 ω) (hrHD_rayPt j (t : ℤ)) := by
-- proof
  apply StatMech.Walls.bc3_mem_clusterNbhd

/--
[bc3_rayPt_mem_clusterNbhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_rayPt_mem_clusterNbhd_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L t : ℕ}
-- given
  (h0 : 1 ≤ t)
  (h1 : t ≤ L) :
-- imply
  hrHD_rayPt j (t : ℤ) ∈ bc3_clusterNbhd ω j L := by
-- proof
  apply StatMech.Walls.bc3_rayPt_mem_clusterNbhd h0 h1

/--
[bc3_mouth_mem_clusterNbhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_mouth_mem_clusterNbhd_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  (hrHD_rayPt j 1 : Site d) ∈ bc3_clusterNbhd ω j L := by
-- proof
  apply StatMech.Walls.bc3_mouth_mem_clusterNbhd hL

/--
[bc3_corridorEdge_structure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_corridorEdge_structure_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {u v : Site d}
-- given
  (h : s(u, v) ∈ hrHD_corridorEdges j L) :
-- imply
  ∃ p : ℕ, p < L ∧ s(u, v) = s(hrHD_rayPt j (p : ℤ), hrHD_rayPt j ((p : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bc3_corridorEdge_structure h

/--
[bc3_sameAxis_step_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_sameAxis_step_mem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Fin d}
  {La : ℕ}
  {u v : Site d}
-- given
  (hno0 : (0 : Site d) ∉ s(u, v))
  (hmem : s(u, v) ∈ hrHD_corridorEdges a (La + 1)) :
-- imply
  v ∈ bc3_clusterNbhd ω a (La + 1) := by
-- proof
  apply StatMech.Walls.bc3_sameAxis_step_mem ω a La hno0 hmem

/--
[bc3_crossAxis_step_absurd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_crossAxis_step_absurd_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a c : Fin d}
  {La Lc : ℕ}
  {u v : Site d}
-- given
  (hcross : bc3_CrossDisjoint ω a c (La + 1) (Lc + 1))
  (hno0 : (0 : Site d) ∉ s(u, v))
  (hu : u ∈ bc3_clusterNbhd ω a (La + 1))
  (hmem : s(u, v) ∈ hrHD_corridorEdges c (Lc + 1)) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.bc3_crossAxis_step_absurd ω a c La Lc hcross hno0 hu hmem

/--
[bc3_clusterNbhd_adjClosed_gen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_clusterNbhd_adjClosed_gen_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a c₁ c₂ : Fin d}
  {La Lc₁ Lc₂ : ℕ}
-- given
  (hcross1 : bc3_CrossDisjoint ω a c₁ (La + 1) (Lc₁ + 1))
  (hcross2 : bc3_CrossDisjoint ω a c₂ (La + 1) (Lc₂ + 1)) :
-- imply
  bc3_AdjClosed (removeSite 0 (forceOpenFinset (hrHD_corridorEdges a (La + 1) ∪ hrHD_corridorEdges c₁ (Lc₁ + 1) ∪ hrHD_corridorEdges c₂ (Lc₂ + 1)) ω)) (bc3_clusterNbhd ω a (La + 1)) := by
-- proof
  apply StatMech.Walls.bc3_clusterNbhd_adjClosed_gen ω a c₁ c₂ La Lc₁ Lc₂ hcross1 hcross2

/--
[bc3_clusterNbhd_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_clusterNbhd_adjClosed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
-- given
  (hcross2 : bc3_CrossDisjoint ω j₁ j₂ (L₁ + 1) (L₂ + 1))
  (hcross3 : bc3_CrossDisjoint ω j₁ j₃ (L₁ + 1) (L₃ + 1)) :
-- imply
  bc3_AdjClosed (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω)) (bc3_clusterNbhd ω j₁ (L₁ + 1)) := by
-- proof
  apply StatMech.Walls.bc3_clusterNbhd_adjClosed ω j₁ j₂ j₃ L₁ L₂ L₃ hcross2 hcross3

/--
[bc3_corridorUnion_perm2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_corridorUnion_perm2_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ} :
-- imply
  bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃ = hrHD_corridorEdges j₂ (L₂ + 1) ∪ hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₃ (L₃ + 1) := by
-- proof
  apply StatMech.Walls.bc3_corridorUnion_perm2 j₁ j₂ j₃ L₁ L₂ L₃

/--
[bc3_corridorUnion_perm3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_corridorUnion_perm3_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ} :
-- imply
  bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃ = hrHD_corridorEdges j₃ (L₃ + 1) ∪ hrHD_corridorEdges j₁ (L₁ + 1) ∪ hrHD_corridorEdges j₂ (L₂ + 1) := by
-- proof
  apply StatMech.Walls.bc3_corridorUnion_perm3 j₁ j₂ j₃ L₁ L₂ L₃

/--
[bc3_mouth_separated_of_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_mouth_separated_of_cross_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
  {q : Site d}
-- given
  (hcross2 : bc3_CrossDisjoint ω j₁ j₂ (L₁ + 1) (L₂ + 1))
  (hcross3 : bc3_CrossDisjoint ω j₁ j₃ (L₁ + 1) (L₃ + 1))
  (hq : q ∉ bc3_clusterNbhd ω j₁ (L₁ + 1)) :
-- imply
  ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω)) (hrHD_rayPt j₁ 1) q := by
-- proof
  apply StatMech.Walls.bc3_mouth_separated_of_cross ω j₁ j₂ j₃ L₁ L₂ L₃ hcross2 hcross3 q hq

/--
[bc3_pairwiseSeparated_of_corridorClustersDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_pairwiseSeparated_of_corridorClustersDisjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
-- given
  (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
-- imply
  bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ := by
-- proof
  apply StatMech.Walls.bc3_pairwiseSeparated_of_corridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ h

/--
[bc3_forcedCorridorRouting_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_forcedCorridorRouting_of_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃)
  (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite)
  (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
-- imply
  bc2_ForcedCorridorRouting ω := by
-- proof
  apply StatMech.Walls.bc3_forcedCorridorRouting_of_disjoint ω hj12 hj13 hj23 hi1 hi2 hi3 h

/--
[bc3_csc_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_csc_of_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃)
  (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((L₁ : ℤ) + 1))).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((L₂ : ℤ) + 1))).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((L₃ : ℤ) + 1))).Infinite)
  (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
-- imply
  csc_DistinctClusterCorridors ω := by
-- proof
  apply StatMech.Walls.bc3_csc_of_disjoint ω hj12 hj13 hj23 hi1 hi2 hi3 h

/--
[bc3_cluster_bot_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_cluster_bot_singleton_eq
  {d : ℕ}
  {x : Site d}
-- given
  (_hx : x ≠ 0) :
-- imply
  cluster d (removeSite 0 (⊥ : ConfigSpace (Sym2 (Site d)))) x = {x} := by
-- proof
  apply StatMech.Walls.bc3_cluster_bot_singleton x _hx

/--
[bc3_crossDisjoint_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_crossDisjoint_bot_eq
  {d : ℕ}
  {a c : Fin d}
  {R L : ℕ}
-- given
  (hac : a ≠ c) :
-- imply
  bc3_CrossDisjoint (⊥ : ConfigSpace (Sym2 (Site d))) a c R L := by
-- proof
  apply StatMech.Walls.bc3_crossDisjoint_bot hac R L

/--
[bc3_corridorClustersDisjoint_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_corridorClustersDisjoint_bot_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃) :
-- imply
  bc3_CorridorClustersDisjoint (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃ := by
-- proof
  apply StatMech.Walls.bc3_corridorClustersDisjoint_bot hj12 hj13 hj23 L₁ L₂ L₃

/--
[bc3_pairwiseSeparated_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean)
-/
@[path]
private lemma bc3_pairwiseSeparated_bot_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃) :
-- imply
  bc2_PairwiseSeparated (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃ := by
-- proof
  apply StatMech.Walls.bc3_pairwiseSeparated_bot hj12 hj13 hj23 L₁ L₂ L₃


-- created on 2026-10-23
