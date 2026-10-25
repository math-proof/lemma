import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc7core
open Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc7_armClosed_corridorEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7core.lean)
-/
@[path]
private lemma bc7_armClosed_corridorEdge_eq
  {d : ℕ}
  {N : ℕ}
  {a c₁ c₂ : Fin d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hac1 : a ≠ c₁)
  (hac2 : a ≠ c₂)
  (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (N + 1) ∪ hrHD_corridorEdges c₂ (N + 1))
  (hf1 : (hrHD_rayPt c₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω)
  (hf2 : (hrHD_rayPt c₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω)
  (hu : u ∈ bc6_offBoxCluster N a (N + 1) ω)
  (hno0 : (0 : Site d) ∉ s(u, v))
  (hGmem : s(u, v) ∈ G) :
-- imply
  v ∈ bc6_rayInterior a (N + 1) := by
-- proof
  apply StatMech.Walls.bc7_armClosed_corridorEdge hac1 hac2 hGdef hf1 hf2 hu hno0 hGmem

/--
[bc7_armClosed_offBoxStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7core.lean)
-/
@[path]
private lemma bc7_armClosed_offBoxStep_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {u v : Site d}
-- given
  (hu : u ∈ bc6_offBoxCluster N a (N + 1) ω)
  (hopen : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v)
  (hG : s(u, v) ∉ G)
  (hbox : s(u, v) ∉ boxEdges d N)
  (hvoff : v ∉ box d N) :
-- imply
  v ∈ bc6_offBoxCluster N a (N + 1) ω := by
-- proof
  apply StatMech.Walls.bc7_armClosed_offBoxStep hu hopen hG hbox hvoff

/--
[bc7_armClosed_of_reentryOnRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7core.lean)
-/
@[path]
private lemma bc7_armClosed_of_reentryOnRay_eq
  {d : ℕ}
  {N : ℕ}
  {a c₁ c₂ : Fin d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
-- given
  (hac1 : a ≠ c₁)
  (hac2 : a ≠ c₂)
  (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (N + 1) ∪ hrHD_corridorEdges c₂ (N + 1))
  (hf1 : (hrHD_rayPt c₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω)
  (hf2 : (hrHD_rayPt c₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω)
  (hre : bc6_ReentryOnRay N a G ω) :
-- imply
  bc6_ArmClosed N a (N + 1) G ω := by
-- proof
  apply StatMech.Walls.bc7_armClosed_of_reentryOnRay hac1 hac2 hGdef hf1 hf2 hre

/--
[bc7_crossFarEnd_of_distinctCutClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7core.lean)
-/
@[path]
private lemma bc7_crossFarEnd_of_distinctCutClusters_eq
  {d : ℕ}
  {N : ℕ}
  {a c : Fin d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hne : cluster d (removeSite 0 ω) (hrHD_rayPt a ((N + 1 : ℕ) : ℤ)) ≠ cluster d (removeSite 0 ω) (hrHD_rayPt c ((N + 1 : ℕ) : ℤ))) :
-- imply
  (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω := by
-- proof
  apply StatMech.Walls.bc7_crossFarEnd_of_distinctCutClusters hne

/--
[bc7_sixCrossFarEnds_of_distinctCutClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7core.lean)
-/
@[path]
private lemma bc7_sixCrossFarEnds_of_distinctCutClusters_eq
  {d : ℕ}
  {N : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h12 : cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ≠ cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)))
  (h13 : cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ≠ cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)))
  (h23 : cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ≠ cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ))) :
-- imply
  (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω ∧ (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω ∧ (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω ∧ (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω ∧ (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω ∧ (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω := by
-- proof
  apply StatMech.Walls.bc7_sixCrossFarEnds_of_distinctCutClusters h12 h13 h23

/--
[bc7_corridorArmsDisjoint_of_reentryOnRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7core.lean)
-/
@[path]
private lemma bc7_corridorArmsDisjoint_of_reentryOnRay_eq
  {d : ℕ}
  {N : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃)
  (hr1 : bc6_ReentryOnRay N j₁ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
  (hr2 : bc6_ReentryOnRay N j₂ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
  (hr3 : bc6_ReentryOnRay N j₃ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
  (hf12 : (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω)
  (hf13 : (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₁ (N + 1) ω)
  (hf21 : (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω)
  (hf23 : (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₂ (N + 1) ω)
  (hf31 : (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω)
  (hf32 : (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N j₃ (N + 1) ω) :
-- imply
  bc6_CorridorArmsDisjoint N j₁ j₂ j₃ ω := by
-- proof
  apply StatMech.Walls.bc7_corridorArmsDisjoint_of_reentryOnRay hj12 hj13 hj23 hr1 hr2 hr3 hf12 hf13 hf21 hf23 hf31 hf32

/--
[bc7_corridorArmsDisjoint_of_reentryOnRay_and_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7core.lean)
-/
@[path]
private lemma bc7_corridorArmsDisjoint_of_reentryOnRay_and_distinct_eq
  {d : ℕ}
  {N : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hj12 : j₁ ≠ j₂)
  (hj13 : j₁ ≠ j₃)
  (hj23 : j₂ ≠ j₃)
  (hr1 : bc6_ReentryOnRay N j₁ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
  (hr2 : bc6_ReentryOnRay N j₂ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
  (hr3 : bc6_ReentryOnRay N j₃ (bc3_corridorUnion j₁ j₂ j₃ N N N) ω)
  (h12 : cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ≠ cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)))
  (h13 : cluster d (removeSite 0 ω) (hrHD_rayPt j₁ ((N + 1 : ℕ) : ℤ)) ≠ cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ)))
  (h23 : cluster d (removeSite 0 ω) (hrHD_rayPt j₂ ((N + 1 : ℕ) : ℤ)) ≠ cluster d (removeSite 0 ω) (hrHD_rayPt j₃ ((N + 1 : ℕ) : ℤ))) :
-- imply
  bc6_CorridorArmsDisjoint N j₁ j₂ j₃ ω := by
-- proof
  apply StatMech.Walls.bc7_corridorArmsDisjoint_of_reentryOnRay_and_distinct hj12 hj13 hj23 hr1 hr2 hr3 h12 h13 h23

/--
[bc7_reentryOnRay_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7core.lean)
-/
@[path]
private lemma bc7_reentryOnRay_bot_eq
  {d : ℕ}
  {N : ℕ}
  {a : Fin d}
  {G : Finset (Sym2 (Site d))} :
-- imply
  bc6_ReentryOnRay N a G (⊥ : ConfigSpace (Sym2 (Site d))) := by
-- proof
  apply StatMech.Walls.bc7_reentryOnRay_bot G

/--
[bc7_corridorArmsDisjoint_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7core.lean)
-/
@[path]
private lemma bc7_corridorArmsDisjoint_bot_eq
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
  apply StatMech.Walls.bc7_corridorArmsDisjoint_bot hj12 hj13 hj23

/--
[bc7_corridorClustersDisjoint_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7core.lean)
-/
@[path]
private lemma bc7_corridorClustersDisjoint_bot_eq
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
  apply StatMech.Walls.bc7_corridorClustersDisjoint_bot hj12 hj13 hj23


-- created on 2026-10-23
