import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc93badbox
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc93_two_infinite_clusters_of_badBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_two_infinite_clusters_of_badBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y' : Site d}
-- given
  (h : bc93_BadBox ω L y') :
-- imply
  ∃ a b : Site d, (cluster d ω a).Infinite ∧ (cluster d ω b).Infinite ∧ cluster d ω a ≠ cluster d ω b := by
-- proof
  apply StatMech.Walls.bc93_two_infinite_clusters_of_badBox ω L h

/--
[bc93_no_badBox_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_no_badBox_of_le_one_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y' : Site d}
-- given
  (hN : numInfiniteClusters d ω ≤ 1) :
-- imply
  ¬ bc93_BadBox ω L y' := by
-- proof
  apply StatMech.Walls.bc93_no_badBox_of_le_one ω L hN y'

/--
[bc93_badBox_free_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_badBox_free_of_le_one_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
-- given
  (hN : numInfiniteClusters d ω ≤ 1) :
-- imply
  ∀ y' : Site d, ¬ bc93_BadBox ω L y' := by
-- proof
  apply StatMech.Walls.bc93_badBox_free_of_le_one ω L hN

/--
[bc93_two_le_numInfinite_of_badBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_two_le_numInfinite_of_badBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y' : Site d}
-- given
  (h : bc93_BadBox ω L y') :
-- imply
  2 ≤ numInfiniteClusters d ω := by
-- proof
  apply StatMech.Walls.bc93_two_le_numInfinite_of_badBox ω L h

/--
[bc93_not_le_one_of_badBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_not_le_one_of_badBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y' : Site d}
-- given
  (h : bc93_BadBox ω L y') :
-- imply
  ¬ numInfiniteClusters d ω ≤ 1 := by
-- proof
  apply StatMech.Walls.bc93_not_le_one_of_badBox ω L h

/--
[bc93_upperLines_witnesses_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_upperLines_witnesses_in_box_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc57_pt (3 * (L : ℤ) + 1) 1 ∈ bc61_boxAround 2 L (bc76_yBuf L) ∧ bc57_pt (3 * (L : ℤ) + 1) 3 ∈ bc61_boxAround 2 L (bc76_yBuf L) := by
-- proof
  apply StatMech.Walls.bc93_upperLines_witnesses_in_box hL

/--
[bc93_singleBox_trif_perConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_singleBox_trif_perConfig_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d} :
-- imply
  bc83_genuineTrif ω L y ↔ bc61_IsCoarseTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc93_singleBox_trif_perConfig ω L y

/--
[bc93_le_one_subset_no_badBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_le_one_subset_no_badBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
-- given
  (hN : numInfiniteClusters d ω ≤ 1) :
-- imply
  ∀ y' : Site d, ¬ bc93_BadBox ω L y' := by
-- proof
  apply StatMech.Walls.bc93_le_one_subset_no_badBox ω L hN

/--
[bc93_no_badBox_ae_of_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_no_badBox_ae_of_uniqueness_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {y' : Site d}
-- given
  (h0 : μ {ω | numInfiniteClusters d ω ≤ 1} = 1) :
-- imply
  ∀ᵐ ω ∂μ, ¬ bc93_BadBox ω L y' := by
-- proof
  apply StatMech.Walls.bc93_no_badBox_ae_of_uniqueness μ L h0 y'

/--
[bc93_bk_from_no_badBox_effect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_bk_from_no_badBox_effect_eq
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
  apply StatMech.Walls.bc93_bk_from_no_badBox_effect μ hd L hinv hforest_ae hexist

/--
[bc93_upperLines_singleBox_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_upperLines_singleBox_trif_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc83_genuineTrif bc60_upperLines L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc93_upperLines_singleBox_trif hL

/--
[bc93_upperLines_multiBox_fails_and_N_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_upperLines_multiBox_fails_and_N_top_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  (bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) ∧ Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc76_yBuf L)) ∧ ((bc76_twoBoxGn L).induce ({(0 : Site 2)}ᶜ : Set (Site 2))).Reachable ⟨bc57_pt ((L : ℤ) + 1) 1, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩ ⟨bc57_pt ((L : ℤ) + 1) 3, by simpa using bc76_pt_ne_zero_of_height (by norm_num)⟩) ∧ numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc93_upperLines_multiBox_fails_and_N_top hL

/--
[bc93_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc93badbox.lean)
-/
@[path]
private lemma bc93_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), bc83_genuineTrif ω L y ↔ bc61_IsCoarseTrifurcation ω L y) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), numInfiniteClusters 2 ω ≤ 1 → ∀ y' : Site 2, ¬ bc93_BadBox ω L y') ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y' : Site 2), bc93_BadBox ω L y' → 2 ≤ numInfiniteClusters 2 ω) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), numInfiniteClusters 2 ω ≤ 1 → ∀ y' : Site 2, ¬ bc93_BadBox ω L y') ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ) (y' : Site 2), μ {ω | numInfiniteClusters 2 ω ≤ 1} = 1 → ∀ᵐ ω ∂μ, ¬ bc93_BadBox ω L y') ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → (∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
-- proof
  apply StatMech.Walls.bc93_status


-- created on 2026-10-23
