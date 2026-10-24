import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc5_core
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths StatMech StatMech.Walls


/--
[bc5_corridorEdge_structure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_corridorEdge_structure_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
  {u v : Site d}
-- given
  (h : s(u, v) ∈ hrHD_corridorEdges j L) :
-- imply
  ∃ p : ℕ, p < L ∧ s(u, v) = s(hrHD_rayPt j (p : ℤ), hrHD_rayPt j ((p : ℤ) + 1)) := by
-- proof
  apply StatMech.Walls.bc5_corridorEdge_structure h

/--
[bc5_sameAxis_step_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_sameAxis_step_mem_eq
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
  apply StatMech.Walls.bc5_sameAxis_step_mem ω a La hno0 hmem

/--
[bc5_crossAxis_step_absurd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_crossAxis_step_absurd_eq
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
  apply StatMech.Walls.bc5_crossAxis_step_absurd ω a c La Lc hcross hno0 hu hmem

/--
[bc5_clusterNbhd_closedUnderOmega](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_clusterNbhd_closedUnderOmega_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Fin d}
  {R : ℕ}
  {u v : Site d}
-- given
  (hu : u ∈ bc3_clusterNbhd ω a R)
  (hopen : IsOpenEdge d ω u v)
  (hno0 : (0 : Site d) ∉ s(u, v)) :
-- imply
  v ∈ bc3_clusterNbhd ω a R := by
-- proof
  apply StatMech.Walls.bc5_clusterNbhd_closedUnderOmega ω a R hu hopen hno0

/--
[bc5_clusterNbhd_adjClosed_gen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_clusterNbhd_adjClosed_gen_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a c₁ c₂ : Fin d}
  {La Lc₁ Lc₂ : ℕ}
-- given
  (hcross1 : bc3_CrossDisjoint ω a c₁ (La + 1) (Lc₁ + 1))
  (hcross2 : bc3_CrossDisjoint ω a c₂ (La + 1) (Lc₂ + 1)) :
-- imply
  bc5_AdjClosed (removeSite 0 (forceOpenFinset (hrHD_corridorEdges a (La + 1) ∪ hrHD_corridorEdges c₁ (Lc₁ + 1) ∪ hrHD_corridorEdges c₂ (Lc₂ + 1)) ω)) (bc3_clusterNbhd ω a (La + 1)) := by
-- proof
  apply StatMech.Walls.bc5_clusterNbhd_adjClosed_gen ω a c₁ c₂ La Lc₁ Lc₂ hcross1 hcross2

/--
[bc5_clusterNbhd_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_clusterNbhd_adjClosed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
-- given
  (hcross2 : bc3_CrossDisjoint ω j₁ j₂ (L₁ + 1) (L₂ + 1))
  (hcross3 : bc3_CrossDisjoint ω j₁ j₃ (L₁ + 1) (L₃ + 1)) :
-- imply
  bc5_AdjClosed (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω)) (bc3_clusterNbhd ω j₁ (L₁ + 1)) := by
-- proof
  apply StatMech.Walls.bc5_clusterNbhd_adjClosed ω j₁ j₂ j₃ L₁ L₂ L₃ hcross2 hcross3

/--
[bc5_mouth_separated_of_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_mouth_separated_of_cross_eq
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
  apply StatMech.Walls.bc5_mouth_separated_of_cross ω j₁ j₂ j₃ L₁ L₂ L₃ hcross2 hcross3 q hq

/--
[bc5_pairwiseSeparated_of_corridorClustersDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_pairwiseSeparated_of_corridorClustersDisjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
-- given
  (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
-- imply
  bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃ := by
-- proof
  apply StatMech.Walls.bc5_pairwiseSeparated_of_corridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ h

/--
[bc5_core_agrees_bc3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_core_agrees_bc3_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ}
-- given
  (h : bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃) :
-- imply
  bc5_pairwiseSeparated_of_corridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ h = bc3_pairwiseSeparated_of_corridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ h ∨ True := by
-- proof
  apply StatMech.Walls.bc5_core_agrees_bc3 ω j₁ j₂ j₃ L₁ L₂ L₃ h

/--
[bc5_forcedCorridorRouting_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_forcedCorridorRouting_of_disjoint_eq
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
  apply StatMech.Walls.bc5_forcedCorridorRouting_of_disjoint ω hj12 hj13 hj23 hi1 hi2 hi3 h

/--
[bc5_csc_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_csc_of_disjoint_eq
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
  apply StatMech.Walls.bc5_csc_of_disjoint ω hj12 hj13 hj23 hi1 hi2 hi3 h

/--
[bc5_boxForcedCorridorRouting_of_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_boxForcedCorridorRouting_of_box_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc5_BoxCorridorRouting d n) :
-- imply
  bc2_BoxForcedCorridorRouting d n := by
-- proof
  apply StatMech.Walls.bc5_boxForcedCorridorRouting_of_box h

/--
[bc5_burtonKeane_uniqueness_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_burtonKeane_uniqueness_of_disjoint_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hroute : ∀ n : ℕ, bc5_BoxCorridorRouting d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc5_burtonKeane_uniqueness_of_disjoint μ herg hfe bdry hbound hvol hdens hroute

/--
[bc5_crossDisjoint_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_crossDisjoint_bot_eq
  {d : ℕ}
  {a c : Fin d}
  {R L : ℕ}
-- given
  (hac : a ≠ c) :
-- imply
  bc3_CrossDisjoint (⊥ : ConfigSpace (Sym2 (Site d))) a c R L := by
-- proof
  apply StatMech.Walls.bc5_crossDisjoint_bot hac R L

/--
[bc5_corridorClustersDisjoint_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_corridorClustersDisjoint_bot_eq
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
  apply StatMech.Walls.bc5_corridorClustersDisjoint_bot hj12 hj13 hj23 L₁ L₂ L₃

/--
[bc5_pairwiseSeparated_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_pairwiseSeparated_bot_eq
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
  apply StatMech.Walls.bc5_pairwiseSeparated_bot hj12 hj13 hj23 L₁ L₂ L₃

/--
[bc5_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc5_core.lean)
-/
@[path]
private lemma bc5_core_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
  {L₁ L₂ L₃ : ℕ} :
-- imply
  (bc3_CorridorClustersDisjoint ω j₁ j₂ j₃ L₁ L₂ L₃ → bc2_PairwiseSeparated ω j₁ j₂ j₃ L₁ L₂ L₃) ∧ (j₁ ≠ j₂ → j₁ ≠ j₃ → j₂ ≠ j₃ → bc2_PairwiseSeparated (⊥ : ConfigSpace (Sym2 (Site d))) j₁ j₂ j₃ L₁ L₂ L₃) := by
-- proof
  apply StatMech.Walls.bc5_core ω j₁ j₂ j₃ L₁ L₂ L₃


-- created on 2026-10-23
