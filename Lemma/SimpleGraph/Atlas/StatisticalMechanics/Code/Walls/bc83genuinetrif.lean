import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc83genuinetrif.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc83_genuineTrif_iff_coarse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_genuineTrif_iff_coarse_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d} :
-- imply
  bc83_genuineTrif ω L y ↔ bc61_IsCoarseTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc83_genuineTrif_iff_coarse ω L y

/--
[bc83_genuineTrifFinset_eq_coarse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_genuineTrifFinset_eq_coarse_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bc83_genuineTrifFinset ω L R = bc61_coarseTrifFinset ω L R := by
-- proof
  apply StatMech.Walls.bc83_genuineTrifFinset_eq_coarse ω L R

/--
[bc83_no_overcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_no_overcount_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ} :
-- imply
  bc83_genuineTrifCount ω L R = bc61_coarseTcount ω L R := by
-- proof
  apply StatMech.Walls.bc83_no_overcount ω L R

/--
[bc83_genuine_branch_le_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_genuine_branch_le_leaf_eq
  {d : ℕ}
  [Fintype W]
  [Nonempty W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bc83_genuine_branch_le_leaf G hacyc hmin

/--
[bc83_genuine_count_le_boundary_of_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_genuine_count_le_boundary_of_forest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc61_CoarseForestLeafCount ω L R) :
-- imply
  bc83_genuineTrifCount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc83_genuine_count_le_boundary_of_forest ω L R h

/--
[bc83_expected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_expected_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L R : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc83_genuineTrif ω L 0} = ∫⁻ ω, (bc83_genuineTrifCount ω L R : ℝ≥0∞) ∂μ := by
-- proof
  apply StatMech.Walls.bc83_expected μ hinv L R

/--
[bc83_prob_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_prob_zero_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R) :
-- imply
  μ {ω | bc83_genuineTrif ω L 0} = 0 := by
-- proof
  apply StatMech.Walls.bc83_prob_zero μ hd L hinv hforest

/--
[bc83_bk_from_genuine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_bk_from_genuine_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (h0 : μ {ω | bc83_genuineTrif ω L 0} = 0)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc83_bk_from_genuine μ hd L hinv h0 hexist

/--
[bc83_bk_from_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_bk_from_forest_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc73_SublatticeForest ω L R)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc83_bk_from_forest μ hd L hinv hforest hexist

/--
[bc83_upperLines_genuineTrif_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_upperLines_genuineTrif_at_zero_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc83_genuineTrif bc60_upperLines L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc83_upperLines_genuineTrif_at_zero hL

/--
[bc83_upperLines_overcount_note](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_upperLines_overcount_note_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ bc83_genuineTrif bc60_upperLines L (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc83_upperLines_overcount_note hL

/--
[bc83_upperLines_N_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_upperLines_N_top_eq
  {d : ℕ} :
-- imply
  numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc83_upperLines_N_top

/--
[bc83_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc83genuinetrif.lean)
-/
@[path]
private lemma bc83_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc83_genuineTrifCount ω L R = bc61_coarseTcount ω L R) ∧ (∀ (W : Type) (_ : Fintype W) (_ : Nonempty W) (G : SimpleGraph W) (_ : DecidableRel G.Adj), G.IsAcyclic → (∀ v, 1 ≤ G.degree v) → (Finset.univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (Finset.univ.filter (fun v => G.degree v = 1)).card) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bc61_CoarseForestLeafCount ω L R → bc83_genuineTrifCount ω L R ≤ boxSV_boundaryCard 2 R) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → μ {ω | bc83_genuineTrif ω L 0} = 0 → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (∀ {L : ℕ}, 3 ≤ L → bc83_genuineTrif bc60_upperLines L (0 : Site 2)) := by
-- proof
  apply StatMech.Walls.bc83_status


-- created on 2026-10-23
