import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc81gncutae
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc81_singleBox_no_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_singleBox_no_gap_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧ (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc81_singleBox_no_gap ω L y h

/--
[bc81_omega_cluster_infinite_of_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_omega_cluster_infinite_of_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a : Site d}
-- given
  (h : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  (cluster d ω a).Infinite := by
-- proof
  apply StatMech.Walls.bc81_omega_cluster_infinite_of_cut ω L y a h

/--
[bc81_cut_cluster_infinite_of_coarse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_cut_cluster_infinite_of_coarse_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite ∧ (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc81_cut_cluster_infinite_of_coarse ω L h

/--
[bc81_infinite_clusters_coincide_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_infinite_clusters_coincide_of_le_one_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (hN : numInfiniteClusters d ω ≤ 1)
  (ha : (cluster d ω a).Infinite)
  (hb : (cluster d ω b).Infinite) :
-- imply
  Connected d ω a b := by
-- proof
  apply StatMech.Walls.bc81_infinite_clusters_coincide_of_le_one ω hN ha hb

/--
[bc81_coarseTrif_arms_connected_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_coarseTrif_arms_connected_of_le_one_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (hN : numInfiniteClusters d ω ≤ 1)
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, Connected d ω a₁ a₂ ∧ Connected d ω a₁ a₃ ∧ Connected d ω a₂ a₃ ∧ (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc81_coarseTrif_arms_connected_of_le_one ω L hN h

/--
[bc81_route2_circular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_route2_circular_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ] :
-- imply
  μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc81_route2_circular μ

/--
[bc81_coarseTrif_consistent_with_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_coarseTrif_consistent_with_le_one_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (hN : numInfiniteClusters d ω ≤ 1)
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧ ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃) ∧ (Connected d ω a₁ a₂ ∧ Connected d ω a₁ a₃ ∧ Connected d ω a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc81_coarseTrif_consistent_with_le_one ω L hN h

/--
[bc81_route1_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_route1_fails_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧ Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧ ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
-- proof
  apply StatMech.Walls.bc81_route1_fails hL

/--
[bc81_leaf_noncircular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_leaf_noncircular_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) :
-- imply
  ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc81_leaf_noncircular μ L hinv h0

/--
[bc81_bk_from_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_bk_from_leaf_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc81_bk_from_leaf μ hd L hinv h0 hexist

/--
[bc81_cardinal_verdict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_cardinal_verdict_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (y : Site d), bc61_IsCoarseTrifurcation ω L y → ∃ a₁ a₂ a₃ : Site d, ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (y : Site d), numInfiniteClusters d ω ≤ 1 → bc61_IsCoarseTrifurcation ω L y → ∃ a₁ a₂ a₃ : Site d, Connected d ω a₁ a₂ ∧ Connected d ω a₁ a₃ ∧ Connected d ω a₂ a₃) ∧ (μ {ω | numInfiniteClusters d ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc81_cardinal_verdict μ hd L hinv

/--
[bc81_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc81gncutae.lean)
-/
@[path]
private lemma bc81_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), bc61_IsCoarseTrifurcation ω L y → ∃ a₁ a₂ a₃ : Site 2, ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), numInfiniteClusters 2 ω ≤ 1 → bc61_IsCoarseTrifurcation ω L y → ∃ a₁ a₂ a₃ : Site 2, Connected 2 ω a₁ a₂ ∧ Connected 2 ω a₁ a₃ ∧ Connected 2 ω a₂ a₃) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], μ {ω | numInfiniteClusters 2 ω < ⊤} = 1 ↔ μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (∀ {L : ℕ}, 3 ≤ L → ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc81_status


-- created on 2026-10-23
