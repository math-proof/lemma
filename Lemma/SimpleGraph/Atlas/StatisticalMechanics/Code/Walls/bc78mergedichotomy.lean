import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc78mergedichotomy
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc78_numInfinite_ae_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_numInfinite_ae_const_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ) :
-- imply
  ∃ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 := by
-- proof
  apply StatMech.Walls.bc78_numInfinite_ae_const μ herg

/--
[bc78_ae_no_coarseTrif_of_prob_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_ae_no_coarseTrif_of_prob_zero_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) :
-- imply
  ∀ᵐ ω ∂μ, ∀ y : Site d, ¬ bc61_IsCoarseTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.bc78_ae_no_coarseTrif_of_prob_zero μ L hinv h0

/--
[bc78_ae_forest_of_ae_no_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_ae_forest_of_ae_no_coarseTrif_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
-- given
  (hno : ∀ᵐ ω ∂μ, ∀ y : Site d, ¬ bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc78_ae_forest_of_ae_no_coarseTrif μ L hno

/--
[bc78_ae_forest_of_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_ae_forest_of_dichotomy_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (h0 : μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) :
-- imply
  ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc78_ae_forest_of_dichotomy μ L hinv h0

/--
[bc78_infinitely_many_excluded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_infinitely_many_excluded_eq
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
  apply StatMech.Walls.bc78_infinitely_many_excluded μ hd L hinv hforest_ae hexist

/--
[bc78_bk_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_bk_closed_eq
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
  apply StatMech.Walls.bc78_bk_closed μ hd L hinv h0 hexist

/--
[bc78_step1_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_step1_uniqueness_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hmerge : μ (atLeastTwoInfinite d) = 0) :
-- imply
  μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc78_step1_uniqueness μ herg hmerge

/--
[bc78_top_null_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_top_null_of_le_one_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hle1 : μ {ω | numInfiniteClusters d ω ≤ 1} = 1) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc78_top_null_of_le_one μ hle1

/--
[bc78_upperLines_isInfinitelyMany](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_upperLines_isInfinitelyMany_eq
  {d : ℕ} :
-- imply
  numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc78_upperLines_isInfinitelyMany

/--
[bc78_upperLines_excluded_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_upperLines_excluded_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
-- given
  (htop : μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) :
-- imply
  μ {ω : ConfigSpace (Sym2 (Site 2)) | ω = bc60_upperLines} = 0 := by
-- proof
  apply StatMech.Walls.bc78_upperLines_excluded_null μ htop

/--
[bc78_upperLines_coarseTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_upperLines_coarseTrif_eq
  {d : ℕ}
  {L : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines L (0 : Site 2) ∧ numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc78_upperLines_coarseTrif hL

/--
[bc78_coarseTrif_not_forces_two_note](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_coarseTrif_not_forces_two_note_eq
  {d : ℕ} :
-- imply
  bc61_IsCoarseTrifurcation bc60_upperLines 3 (0 : Site 2) ∧ numInfiniteClusters 2 bc60_upperLines = ⊤ := by
-- proof
  apply StatMech.Walls.bc78_coarseTrif_not_forces_two_note

/--
[bc78_circularity_verdict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_circularity_verdict_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ ((μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0) → ∀ R : ℕ, ∀ᵐ ω ∂μ, bc73_SublatticeForest ω L R) := by
-- proof
  apply StatMech.Walls.bc78_circularity_verdict μ hd L hinv

/--
[bc78_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc78mergedichotomy.lean)
-/
@[path]
private lemma bc78_status_eq
  {d : ℕ} :
-- imply
  (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ] (L : ℕ), IsTranslationInvariant (G := Multiplicative (Site 2)) μ → μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], IsErgodic (G := Multiplicative (Site 2)) μ → μ (atLeastTwoInfinite 2) = 0 → μ {ω | numInfiniteClusters 2 ω ≤ 1} = 1) ∧ (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
-- proof
  apply StatMech.Walls.bc78_status


-- created on 2026-10-23
