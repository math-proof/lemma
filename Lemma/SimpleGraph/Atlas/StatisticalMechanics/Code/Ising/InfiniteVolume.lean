import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
open MeasureTheory Filter Topology StatMech StatMech.Ising


/--
[mem_boxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma mem_boxFinset_eq
  {d : ℕ}
  {d n : ℕ}
  {x : Site d} :
-- imply
  x ∈ boxFinset d n ↔ x ∈ box d n := by
-- proof
  apply StatMech.Ising.mem_boxFinset

/--
[glue_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma glue_mem_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {x : Site d}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (hx : x ∈ box d n) :
-- imply
  glue η τ x = τ ⟨x, hx⟩ := by
-- proof
  apply StatMech.Ising.glue_mem η τ hx

/--
[glue_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma glue_not_mem_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {x : Site d}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (hx : x ∉ box d n) :
-- imply
  glue η τ x = η x := by
-- proof
  apply StatMech.Ising.glue_not_mem η τ hx

/--
[fvWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma fvWeight_pos_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  0 < fvWeight η n B β h τ := by
-- proof
  apply StatMech.Ising.fvWeight_pos η n B β h τ

/--
[fvWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma fvWeight_nonneg_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  0 ≤ fvWeight η n B β h τ := by
-- proof
  apply StatMech.Ising.fvWeight_nonneg η n B β h τ

/--
[fvZ_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma fvZ_pos_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  0 < fvZ η n B β h := by
-- proof
  apply StatMech.Ising.fvZ_pos η n B β h

/--
[fvZ_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma fvZ_ne_zero_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  fvZ η n B β h ≠ 0 := by
-- proof
  apply StatMech.Ising.fvZ_ne_zero η n B β h

/--
[fvProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma fvProb_nonneg_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  0 ≤ fvProb η n B β h τ := by
-- proof
  apply StatMech.Ising.fvProb_nonneg η n B β h τ

/--
[fvProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma fvProb_sum_eq_one_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  ∑ τ : {x // x ∈ box d n} → Bool, fvProb η n B β h τ = 1 := by
-- proof
  apply StatMech.Ising.fvProb_sum_eq_one η n B β h

/--
[fvMeasure_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma fvMeasure_univ_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  (fvMeasure η n B β h) Set.univ = 1 := by
-- proof
  apply StatMech.Ising.fvMeasure_univ η n B β h

/--
[exists_infiniteVolumeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma exists_infiniteVolumeState_eq
  {d : ℕ}
  {ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))} :
-- imply
  ∃ μ : ProbabilityMeasure (ConfigSpace (Site d)), InfiniteVolumeState ρ μ := by
-- proof
  apply StatMech.Ising.exists_infiniteVolumeState ρ

/--
[limitState_isInfiniteVolumeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma limitState_isInfiniteVolumeState_eq
  {d : ℕ}
  {ρ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))} :
-- imply
  InfiniteVolumeState ρ (limitState ρ) := by
-- proof
  apply StatMech.Ising.limitState_isInfiniteVolumeState ρ

/--
[plusState_isInfiniteVolumeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma plusState_isInfiniteVolumeState_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (β h : ℝ) :
-- imply
  InfiniteVolumeState (fun n => plusMeasure d n β h) (plusState d β h) := by
-- proof
  apply StatMech.Ising.plusState_isInfiniteVolumeState d β h

/--
[minusState_isInfiniteVolumeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma minusState_isInfiniteVolumeState_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (β h : ℝ) :
-- imply
  InfiniteVolumeState (fun n => minusMeasure d n β h) (minusState d β h) := by
-- proof
  apply StatMech.Ising.minusState_isInfiniteVolumeState d β h

/--
[freeState_isInfiniteVolumeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/InfiniteVolume.lean)
-/
@[path]
private lemma freeState_isInfiniteVolumeState_eq
  {d : ℕ}
  {d : ℕ}
-- given
  (β h : ℝ) :
-- imply
  InfiniteVolumeState (fun n => freeMeasure d n β h) (freeState d β h) := by
-- proof
  apply StatMech.Ising.freeState_isInfiniteVolumeState d β h


-- created on 2026-10-23
