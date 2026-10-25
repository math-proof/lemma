import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc82singleboxcount
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc82_dc_expectation_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc82singleboxcount.lean)
-/
@[path]
private lemma bc82_dc_expectation_identity_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L R : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ := by
-- proof
  apply StatMech.Walls.bc82_dc_expectation_identity μ hinv L R

/--
[bc82_coarseTcount_le_volume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc82singleboxcount.lean)
-/
@[path]
private lemma bc82_coarseTcount_le_volume_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bc61_coarseTcount ω L R ≤ (boxFinsetBK d R).card := by
-- proof
  apply StatMech.Walls.bc82_coarseTcount_le_volume ω L R

/--
[bc82_coarseTcount_eq_volume_of_all_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc82singleboxcount.lean)
-/
@[path]
private lemma bc82_coarseTcount_eq_volume_of_all_trif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hall : ∀ y ∈ boxFinsetBK d R, bc61_IsCoarseTrifurcation ω L y) :
-- imply
  bc61_coarseTcount ω L R = (boxFinsetBK d R).card := by
-- proof
  apply StatMech.Walls.bc82_coarseTcount_eq_volume_of_all_trif ω L R hall

/--
[bc82_singleBox_gives_no_count_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc82singleboxcount.lean)
-/
@[path]
private lemma bc82_singleBox_gives_no_count_bound_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (hall : ∀ y ∈ boxFinsetBK d R, bc61_IsCoarseTrifurcation ω L y) :
-- imply
  (∀ y ∈ boxFinsetBK d R, ∃ a₁ a₂ a₃ : Site d, ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧ bc61_coarseTcount ω L R = (boxFinsetBK d R).card := by
-- proof
  apply StatMech.Walls.bc82_singleBox_gives_no_count_bound ω L R hall

/--
[bc82_expected_needs_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc82singleboxcount.lean)
-/
@[path]
private lemma bc82_expected_needs_upper_bound_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {bdry : ℕ → ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc61_coarseTcount ω L R ≤ bdry R)
  (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
  (hdens : Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0)) :
-- imply
  μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 := by
-- proof
  apply StatMech.Walls.bc82_expected_needs_upper_bound μ L bdry hinv hbound hvol hdens

/--
[bc82_dc_count_is_forest_not_masstransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc82singleboxcount.lean)
-/
@[path]
private lemma bc82_dc_count_is_forest_not_masstransport_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc73_SublatticeForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc82_dc_count_is_forest_not_masstransport ω L R h

/--
[bc82_borelCantelli_route_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc82singleboxcount.lean)
-/
@[path]
private lemma bc82_borelCantelli_route_fails_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧ Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧ ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ := by
-- proof
  apply StatMech.Walls.bc82_borelCantelli_route_fails hL

/--
[bc82_leaf_noncircular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc82singleboxcount.lean)
-/
@[path]
private lemma bc82_leaf_noncircular_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) :
-- imply
  ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc82_leaf_noncircular μ L hinv h0

/--
[bc82_bk_from_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc82singleboxcount.lean)
-/
@[path]
private lemma bc82_bk_from_leaf_eq
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
  apply StatMech.Walls.bc82_bk_from_leaf μ hd L hinv h0 hexist

/--
[bc82_cardinal_verdict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc82singleboxcount.lean)
-/
@[path]
private lemma bc82_cardinal_verdict_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  (∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R → bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ d * boxSV_boundaryCard d R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), (∀ y ∈ boxFinsetBK d R, bc61_IsCoarseTrifurcation ω L y) → bc61_coarseTcount ω L R = (boxFinsetBK d R).card) ∧ ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc82_cardinal_verdict μ hd L hinv

/--
[bc82_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc82singleboxcount.lean)
-/
@[path]
private lemma bc82_status_eq
  {d : ℕ} :
-- imply
  (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (L R : ℕ), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → ((boxFinsetBK 2 R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc73_SublatticeForest ω L R → bc61_coarseTcount ω L R ≤ (2 * L + 1) ^ 2 * boxSV_boundaryCard 2 R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), (∀ y ∈ boxFinsetBK 2 R, bc61_IsCoarseTrifurcation ω L y) → (∀ y ∈ boxFinsetBK 2 R, ∃ a₁ a₂ a₃ : Site 2, ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧ ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) ∧ bc61_coarseTcount ω L R = (boxFinsetBK 2 R).card) ∧ (∀ {L : ℕ}, 3 ≤ L → ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc82_status


-- created on 2026-10-23
