import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bpeprobcount
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bpe_coarseTrif_prob_eq_zero_of_expBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpeprobcount.lean)
-/
@[path]
private lemma bpe_coarseTrif_prob_eq_zero_of_expBound_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {bdry : ℕ → ℕ}
-- given
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hExpBound : ∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞))
  (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
  (hdens : Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0)) :
-- imply
  μ {ω | bc61_IsCoarseTrifurcation ω L 0} = 0 := by
-- proof
  apply StatMech.Walls.bpe_coarseTrif_prob_eq_zero_of_expBound μ L bdry hexp hExpBound hvol hdens

/--
[bpe_top_null_of_expCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpeprobcount.lean)
-/
@[path]
private lemma bpe_top_null_of_expCount_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {bdry : ℕ → ℕ}
-- given
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hExpBound : ∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞))
  (hvol : ∀ R, 0 < (boxFinsetBK d R).card)
  (hdens : Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bpe_top_null_of_expCount μ L bdry hexp hExpBound hvol hdens hexist

/--
[bpe_coarseTcount_le_leafCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpeprobcount.lean)
-/
@[path]
private lemma bpe_coarseTcount_le_leafCard_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R m : ℕ}
-- given
  (h : bpe_CoarseForestNoBnd ω L R m) :
-- imply
  bc61_coarseTcount ω L R ≤ m := by
-- proof
  apply StatMech.Walls.bpe_coarseTcount_le_leafCard ω L R m h

/--
[bpe_noBnd_of_fullForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpeprobcount.lean)
-/
@[path]
private lemma bpe_noBnd_of_fullForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc61_CoarseForestLeafCount ω L R) :
-- imply
  bpe_CoarseForestNoBnd ω L R (boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bpe_noBnd_of_fullForest ω L R h

/--
[bpe_expBound_of_perConfigLeaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpeprobcount.lean)
-/
@[path]
private lemma bpe_expBound_of_perConfigLeaf_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {L : ℕ}
  {bdry : ℕ → ℕ}
  {leafBd : ConfigSpace (Sym2 (Site d)) → ℕ → ℕ}
-- given
  (hle : ∀ ω R, bc61_coarseTcount ω L R ≤ leafBd ω R)
  (hExp : ∀ R, ∫⁻ ω, (leafBd ω R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞)) :
-- imply
  ∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞) := by
-- proof
  apply StatMech.Walls.bpe_expBound_of_perConfigLeaf μ L bdry leafBd hle hExp

/--
[bpe_top_null_of_probForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpeprobcount.lean)
-/
@[path]
private lemma bpe_top_null_of_probForest_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {bdry : ℕ → ℕ}
  {leafBd : ConfigSpace (Sym2 (Site d)) → ℕ → ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hd : 1 ≤ d)
  (hforest : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bpe_CoarseForestNoBnd ω L R (leafBd ω R))
  (hExpLeaf : ∀ R, ∫⁻ ω, (leafBd ω R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞))
  (hdens : Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0))
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bpe_top_null_of_probForest μ hinv hd L bdry leafBd hforest hExpLeaf hdens hexist

/--
[bpe_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpeprobcount.lean)
-/
@[path]
private lemma bpe_status_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
  {bdry : ℕ → ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hd : 1 ≤ d) :
-- imply
  ((∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ) → (∀ R : ℕ, ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞)) → (∀ R, 0 < (boxFinsetBK d R).card) → Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (R m : ℕ), bpe_CoarseForestNoBnd ω L R m → bc61_coarseTcount ω L R ≤ m) ∧ (∀ (leafBd : ConfigSpace (Sym2 (Site d)) → ℕ → ℕ), (∀ ω R, bpe_CoarseForestNoBnd ω L R (leafBd ω R)) → (∀ R, ∫⁻ ω, (leafBd ω R : ℝ≥0∞) ∂μ ≤ (bdry R : ℝ≥0∞)) → Filter.Tendsto (fun R => (bdry R : ℝ) / ((boxFinsetBK d R).card : ℝ)) Filter.atTop (nhds 0) → bc61_CoarseTrifExistence μ L → μ {ω | numInfiniteClusters d ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bpe_status μ hinv hd L bdry


-- created on 2026-10-23
