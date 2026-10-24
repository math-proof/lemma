import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc6core
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc6_rayPt_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_rayPt_mem_box_eq
  {d : ℕ}
  {a : Fin d}
  {N p : ℕ}
-- given
  (hp : p ≤ N) :
-- imply
  (hrHD_rayPt a (p : ℤ)) ∈ box d N := by
-- proof
  apply StatMech.Walls.bc6_rayPt_mem_box hp

/--
[bc6_origin_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_origin_mem_box_eq
  {d : ℕ}
  {N : ℕ} :
-- imply
  (0 : Site d) ∈ box d N := by
-- proof
  apply StatMech.Walls.bc6_origin_mem_box

/--
[bc6_adj_exists_unique_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_adj_exists_unique_diff_eq
  {d : ℕ}
  {x y : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  ∃ k : Fin d, (x k - y k).natAbs = 1 ∧ ∀ i, i ≠ k → x i = y i := by
-- proof
  apply StatMech.Walls.bc6_adj_exists_unique_diff hadj

/--
[bc6_rayPt_offBox_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_rayPt_offBox_neighbor_eq
  {d : ℕ}
  {a : Fin d}
  {N s : ℕ}
  {v : Site d}
-- given
  (hs1 : 1 ≤ s)
  (hsN : s ≤ N)
  (hadj : (hypercubicLattice d).Adj (hrHD_rayPt a (s : ℤ)) v)
  (hvbox : v ∉ box d N) :
-- imply
  s = N ∧ v = hrHD_rayPt a ((s : ℤ) + 1) := by
-- proof
  apply StatMech.Walls.bc6_rayPt_offBox_neighbor hs1 hsN hadj hvbox

/--
[bc6_offBox_rho_edge_to_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_offBox_rho_edge_to_removeSite_eq
  {d : ℕ}
  {N : ℕ}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hopen : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v)
  (hG : s(u, v) ∉ G)
  (hbox : s(u, v) ∉ boxEdges d N) :
-- imply
  IsOpenEdge d (removeSite 0 ω) u v := by
-- proof
  apply StatMech.Walls.bc6_offBox_rho_edge_to_removeSite hopen hG hbox

/--
[bc6_armRegion_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_armRegion_adjClosed_eq
  {d : ℕ}
  {N : ℕ}
  {a c₁ c₂ : Fin d}
  {Lc₁ Lc₂ : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
-- given
  (hac1 : a ≠ c₁)
  (hac2 : a ≠ c₂)
  (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (Lc₁ + 1) ∪ hrHD_corridorEdges c₂ (Lc₂ + 1))
  (harm : bc6_ArmClosed N a (N + 1) G ω) :
-- imply
  bc3_AdjClosed (removeSite 0 (bc6_closeBoxExcept N G ω)) (bc6_armRegion N a (N + 1) ω) := by
-- proof
  apply StatMech.Walls.bc6_armRegion_adjClosed hac1 hac2 G hGdef harm

/--
[bc6_crossRayPt_notMem_armRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_crossRayPt_notMem_armRegion_eq
  {d : ℕ}
  {N : ℕ}
  {a c : Fin d}
  {p : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hac : a ≠ c)
  (hp1 : 1 ≤ p)
  (hpR : p ≤ N + 1)
  (hfar : (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω) :
-- imply
  (hrHD_rayPt c (p : ℤ)) ∉ bc6_armRegion N a (N + 1) ω := by
-- proof
  apply StatMech.Walls.bc6_crossRayPt_notMem_armRegion hac hp1 hpR ω hfar

/--
[bc6_crossDisjoint_of_armClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_crossDisjoint_of_armClosed_eq
  {d : ℕ}
  {N : ℕ}
  {a c₁ c₂ : Fin d}
  {Lc₂ : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
-- given
  (hac1 : a ≠ c₁)
  (hac2 : a ≠ c₂)
  (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (N + 1) ∪ hrHD_corridorEdges c₂ (Lc₂ + 1))
  (harm : bc6_ArmClosed N a (N + 1) G ω)
  (hfar : (hrHD_rayPt c₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω) :
-- imply
  bc3_CrossDisjoint (bc6_closeBoxExcept N G ω) a c₁ (N + 1) (N + 1) := by
-- proof
  apply StatMech.Walls.bc6_crossDisjoint_of_armClosed hac1 hac2 G hGdef harm hfar

/--
[bc6_wiring_perm1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_wiring_perm1_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {N : ℕ} :
-- imply
  bc3_corridorUnion j₁ j₂ j₃ N N N = hrHD_corridorEdges j₁ (N + 1) ∪ hrHD_corridorEdges j₂ (N + 1) ∪ hrHD_corridorEdges j₃ (N + 1) := by
-- proof
  apply StatMech.Walls.bc6_wiring_perm1 j₁ j₂ j₃ N

/--
[bc6_wiring_perm2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_wiring_perm2_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {N : ℕ} :
-- imply
  bc3_corridorUnion j₁ j₂ j₃ N N N = hrHD_corridorEdges j₂ (N + 1) ∪ hrHD_corridorEdges j₁ (N + 1) ∪ hrHD_corridorEdges j₃ (N + 1) := by
-- proof
  apply StatMech.Walls.bc6_wiring_perm2 j₁ j₂ j₃ N

/--
[bc6_wiring_perm3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_wiring_perm3_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {N : ℕ} :
-- imply
  bc3_corridorUnion j₁ j₂ j₃ N N N = hrHD_corridorEdges j₃ (N + 1) ∪ hrHD_corridorEdges j₁ (N + 1) ∪ hrHD_corridorEdges j₂ (N + 1) := by
-- proof
  apply StatMech.Walls.bc6_wiring_perm3 j₁ j₂ j₃ N

/--
[bc6_corridorClustersDisjoint_of_armClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_corridorClustersDisjoint_of_armClosed_eq
  {d : ℕ}
  {N : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃)
  (h : bc6_CorridorArmsDisjoint N j₁ j₂ j₃ ω) :
-- imply
  bc3_CorridorClustersDisjoint (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N) ω) j₁ j₂ j₃ N N N := by
-- proof
  apply StatMech.Walls.bc6_corridorClustersDisjoint_of_armClosed hj12 hj13 hj23 h

/--
[bc6_pairwiseSeparated_of_armClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_pairwiseSeparated_of_armClosed_eq
  {d : ℕ}
  {N : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃)
  (h : bc6_CorridorArmsDisjoint N j₁ j₂ j₃ ω) :
-- imply
  bc2_PairwiseSeparated (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N) ω) j₁ j₂ j₃ N N N := by
-- proof
  apply StatMech.Walls.bc6_pairwiseSeparated_of_armClosed hj12 hj13 hj23 h

/--
[bc6_bot_no_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_bot_no_adj_eq
  {d : ℕ}
  {S : Set (Site d)}
  {x y : S} :
-- imply
  ¬ (openSubgraphInduce d (removeSite 0 (⊥ : ConfigSpace (Sym2 (Site d)))) S).Adj x y := by
-- proof
  apply StatMech.Walls.bc6_bot_no_adj x y

/--
[bc6_bot_walk_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_bot_walk_eq_eq
  {d : ℕ}
  {S : Set (Site d)}
  {x y : S}
  {w : (openSubgraphInduce d (removeSite 0 (⊥ : ConfigSpace (Sym2 (Site d)))) S).Walk x y} :
-- imply
  x = y := by
-- proof
  apply StatMech.Walls.bc6_bot_walk_eq w

/--
[bc6_offBoxCluster_bot_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_offBoxCluster_bot_eq_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {R : ℕ}
  {x : Site d}
-- given
  (hx : x ∈ bc6_offBoxCluster N a R (⊥ : ConfigSpace (Sym2 (Site d)))) :
-- imply
  x = hrHD_rayPt a (R : ℤ) := by
-- proof
  apply StatMech.Walls.bc6_offBoxCluster_bot_eq hx

/--
[bc6_armClosed_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_armClosed_bot_eq
  {d : ℕ}
  {N : ℕ}
  {a c₁ c₂ : Fin d}
  {Lc₁ Lc₂ : ℕ}
  {G : Finset (Sym2 (Site d))}
-- given
  (hac1 : a ≠ c₁)
  (hac2 : a ≠ c₂)
  (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (Lc₁ + 1) ∪ hrHD_corridorEdges c₂ (Lc₂ + 1)) :
-- imply
  bc6_ArmClosed N a (N + 1) G (⊥ : ConfigSpace (Sym2 (Site d))) := by
-- proof
  apply StatMech.Walls.bc6_armClosed_bot hac1 hac2 G hGdef

/--
[bc6_crossFarEnd_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_crossFarEnd_bot_eq
  {d : ℕ}
  {N : ℕ}
  {a c : Fin d}
-- given
  (hac : a ≠ c) :
-- imply
  (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) (⊥ : ConfigSpace (Sym2 (Site d))) := by
-- proof
  apply StatMech.Walls.bc6_crossFarEnd_bot hac

/--
[bc6_corridorArmsDisjoint_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_corridorArmsDisjoint_bot_eq
  {d : ℕ}
  {N : ℕ}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃) :
-- imply
  bc6_CorridorArmsDisjoint N j₁ j₂ j₃ (⊥ : ConfigSpace (Sym2 (Site d))) := by
-- proof
  apply StatMech.Walls.bc6_corridorArmsDisjoint_bot hj12 hj13 hj23

/--
[bc6_corridorClustersDisjoint_closeBox_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_corridorClustersDisjoint_closeBox_bot_eq
  {d : ℕ}
  {N : ℕ}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃) :
-- imply
  bc3_CorridorClustersDisjoint (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N) (⊥ : ConfigSpace (Sym2 (Site d)))) j₁ j₂ j₃ N N N := by
-- proof
  apply StatMech.Walls.bc6_corridorClustersDisjoint_closeBox_bot hj12 hj13 hj23

/--
[bc6_pairwiseSeparated_closeBox_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean)
-/
@[path]
private lemma bc6_pairwiseSeparated_closeBox_bot_eq
  {d : ℕ}
  {N : ℕ}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃) :
-- imply
  bc2_PairwiseSeparated (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N) (⊥ : ConfigSpace (Sym2 (Site d)))) j₁ j₂ j₃ N N N := by
-- proof
  apply StatMech.Walls.bc6_pairwiseSeparated_closeBox_bot hj12 hj13 hj23


-- created on 2026-10-23
