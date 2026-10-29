import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc104consolidation
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc104_bk_uniqueness_of_boxMenger](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_bk_uniqueness_of_boxMenger_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hattach : ∀ n : ℕ, bmm_BoxMengerAttachment d n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc104_bk_uniqueness_of_boxMenger hd p hp1 hp0 hattach

/--
[bc104_dc_step1_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_dc_step1_uniqueness_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
  (hexist : bc61_CoarseTrifExistence μ L)
  (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
-- imply
  μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc104_dc_step1_uniqueness μ hd L herg hfe hinv hforest_ae hexist hmergeGeom

/--
[bc104_dc_bootstrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_dc_bootstrap_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc104_dc_bootstrap μ hd L hinv hforest_ae hexist

/--
[bc104_badBox_forces_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_badBox_forces_two_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y' : Site d}
-- given
  (h : bc93_BadBox ω L y') :
-- imply
  2 ≤ numInfiniteClusters d ω := by
-- proof
  apply StatMech.Walls.bc104_badBox_forces_two ω L h

/--
[bc104_count_bound_under_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_count_bound_under_top_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hN : numInfiniteClusters d ω = ⊤)
  (h : bst_BoxOpenForest ω n) :
-- imply
  bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc104_count_bound_under_top ω n hN h

/--
[bc104_coarse_count_from_connectedForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_coarse_count_from_connectedForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc104_coarse_count_from_connectedForest ω L R h

/--
[bc104_complete_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_complete_chain_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (∀ (p : NNReal) (hp1 : p ≤ 1), 0 < p → (∀ n : ℕ, bmm_BoxMengerAttachment d n) → bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ), IsErgodic (G := Multiplicative (Site d)) μ → HasFiniteEnergyMerge μ → IsTranslationInvariant (G := Multiplicative (Site d)) μ → (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → (∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) → μ {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y' : Site d), bc93_BadBox ω L y' → 2 ≤ numInfiniteClusters d ω) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), numInfiniteClusters d ω = ⊤ → bst_BoxOpenForest ω n → bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc104_complete_chain hd

/--
[bc104_bc56_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_bc56_refuted_eq
  {d : ℕ} :
-- imply
  ¬ bc56_BoxClusterReachesNbr 2 3 := by
-- proof
  apply StatMech.Walls.bc104_bc56_refuted

/--
[bc104_bc56_notFree_of_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_bc56_notFree_of_coarseTrif_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ ¬ bc56_BoxClusterReachesNbr 2 3 := by
-- proof
  apply StatMech.Walls.bc104_bc56_notFree_of_coarseTrif hL

/--
[bc104_bc64_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_bc64_refuted_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bc104_bc64_refuted L

/--
[bc104_bc64_disjointStar_degrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_bc64_disjointStar_degrees_eq
  {d : ℕ} :
-- imply
  bc64_starG.degree 0 = 3 ∧ (∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1) := by
-- proof
  apply StatMech.Walls.bc104_bc64_disjointStar_degrees

/--
[bc104_bc69_count_derivable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_bc69_count_derivable_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc104_bc69_count_derivable ω L R h

/--
[bc104_residue_evolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_residue_evolution_eq
  {d : ℕ} :
-- imply
  (¬ bc56_BoxClusterReachesNbr 2 3) ∧ (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧ (bc64_starG.degree 0 = 3 ∧ (∀ i : Fin 4, i ≠ 0 → bc64_starG.degree i = 1)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc104_residue_evolution

/--
[bc104_proved_dc_bootstrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_proved_dc_bootstrap_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hforest_ae : ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc104_proved_dc_bootstrap μ hd L hinv hforest_ae hexist

/--
[bc104_proved_leaf_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_proved_leaf_count_eq
  {d : ℕ}
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bc104_proved_leaf_count G hacyc hmin

/--
[bc104_proved_branch_le_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_proved_branch_le_leaf_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  [Nonempty (↑S : Type)]
-- given
  (hmin : ∀ v : (↑S : Type), 1 ≤ (bc75_spanForest ω L R c S).degree v) :
-- imply
  (bc80_branchFinset ω L R c S).card ≤ (bc80_leafFinset ω L R c S).card := by
-- proof
  apply StatMech.Walls.bc104_proved_branch_le_leaf ω L R c S hmin

/--
[bc104_proved_leaf_boundary_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_proved_leaf_boundary_free_eq
  {d : ℕ}
  {p : Site d → Prop}
  {S : Set (Subtype p)} :
-- imply
  Set.InjOn (Subtype.val : Subtype p → Site d) S := by
-- proof
  apply StatMech.Walls.bc104_proved_leaf_boundary_free S

/--
[bc104_proved_three_incident_arms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_proved_three_incident_arms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧ ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧ (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧ (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧ (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc104_proved_three_incident_arms ω L y h

/--
[bc104_proved_spanForest_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_proved_spanForest_exists_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc89_GenuineTrif d ω x)
  (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
  (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
-- imply
  bst_BoxOpenForest ω n := by
-- proof
  apply StatMech.Walls.bc104_proved_spanForest_exists ω n hn hcanon harmbox hexists

/--
[bc104_proved_fragments](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_proved_fragments_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site d)) μ → (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧ (∀ (R : ℕ) (S : Set (↑(box d R) : Type)), Set.InjOn (Subtype.val : (↑(box d R) : Type) → Site d) S) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d), bc61_IsCoarseTrifurcation ω L y → ∃ a₁ a₂ a₃ : Site d, (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧ (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃)) := by
-- proof
  apply StatMech.Walls.bc104_proved_fragments hd

/--
[bc104_refuted_singleSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_refuted_singleSite_eq
  {d : ℕ} :
-- imply
  ¬ bc56_BoxClusterReachesNbr 2 3 := by
-- proof
  apply StatMech.Walls.bc104_refuted_singleSite

/--
[bc104_refuted_disjointStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_refuted_disjointStar_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bc104_refuted_disjointStar L

/--
[bc104_refuted_straightAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_refuted_straightAxis_eq
  {d : ℕ}
  {j : Fin 2} :
-- imply
  ¬ crr_ClusterRunsAlongAxis bc56_offAxisLine (bc56_lp 0) j := by
-- proof
  apply StatMech.Walls.bc104_refuted_straightAxis j

/--
[bc104_refuted_twoTerminalMenger](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_refuted_twoTerminalMenger_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hinj : bc64_CoarseBoundaryInjection ω L R) :
-- imply
  bc61_CoarseForestLeafCount ω L R := by
-- proof
  apply StatMech.Walls.bc104_refuted_twoTerminalMenger ω L R hz₀ hz₁ hzne hinj

/--
[bc104_refuted_finiteN_conditioning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_refuted_finiteN_conditioning_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ] :
-- imply
  μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc104_refuted_finiteN_conditioning μ

/--
[bc104_refuted_routes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_refuted_routes_eq
  {d : ℕ} :
-- imply
  (¬ bc56_BoxClusterReachesNbr 2 3) ∧ (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧ (∀ j : Fin 2, ¬ crr_ClusterRunsAlongAxis bc56_offAxisLine (bc56_lp 0) j) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ], μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc104_refuted_routes

/--
[bc104_residue_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_residue_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc104_residue_nonvacuous ω L R hz₀ hz₁ hzne hno

/--
[bc104_residue_closes_bk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_residue_closes_bk_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hGlobal : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc104_residue_closes_bk μ hd hinv hfe L hGlobal hcoarseRoute

/--
[bc104_minimal_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_minimal_residue_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (hfe : HasFiniteEnergyMerge μ) (L : ℕ), (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R) → (0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) → μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) → bc69_Gn_globalForest ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc104_minimal_residue hd

/--
[bc104_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc104consolidation.lean)
-/
@[path]
private lemma bc104_status_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (∀ (p : NNReal) (hp1 : p ≤ 1), 0 < p → (∀ n : ℕ, bmm_BoxMengerAttachment d n) → bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site d)) μ → (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ ((¬ bc56_BoxClusterReachesNbr 2 3) ∧ (∀ (L : ℕ), Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc69_Gn_globalForest ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R)) ∧ (∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj], G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card) ∧ ((∀ (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) (hfe : HasFiniteEnergyMerge μ) (L : ℕ), (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc69_Gn_globalForest ω L R) → (0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) → μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (z₀ z₁ : Site d), z₀ ∈ vertexBoundary d R → z₁ ∈ vertexBoundary d R → z₀ ≠ z₁ → (∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) → bc69_Gn_globalForest ω L R)) := by
-- proof
  apply StatMech.Walls.bc104_status hd


-- created on 2026-10-23
