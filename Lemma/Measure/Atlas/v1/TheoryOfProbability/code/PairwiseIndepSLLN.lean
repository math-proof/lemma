import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfProbability.code.PairwiseIndepSLLN
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal MeasureTheory


/--
[partialSumIndicators_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma partialSumIndicators_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {n : ℕ} :
-- imply
  partialSumIndicators A n = ∑ i ∈ Finset.range n, (A i).indicator (1 : Ω → ℝ) := by
-- proof
  ext ω; simp only [partialSumIndicators, Finset.sum_apply]

/--
[comap_indicator_one_le_generateFrom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma comap_indicator_one_le_generateFrom
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {s : Set Ω} :
-- imply
  MeasurableSpace.comap (s.indicator (1 : Ω → ℝ)) Real.measurableSpace ≤ MeasurableSpace.generateFrom {s} := by
-- proof
  intro t ht
  rw [MeasurableSpace.measurableSet_comap] at ht
  obtain ⟨u, _, rfl⟩ := ht
  classical
  change MeasurableSet[MeasurableSpace.generateFrom {s}]
    ((s.indicator (fun _ => (1 : ℝ))) ⁻¹' u)
  rw [indicator_const_preimage_eq_union s u (1 : ℝ)]
  have hs : MeasurableSet[MeasurableSpace.generateFrom {s}] s :=
    MeasurableSpace.measurableSet_generateFrom (mem_singleton _)
  apply MeasurableSet.union
  · split_ifs
    · exact hs
    · exact @MeasurableSet.empty _ (MeasurableSpace.generateFrom {s})
  · split_ifs
    · exact hs.compl
    · exact @MeasurableSet.empty _ (MeasurableSpace.generateFrom {s})

/--
[indepFun_indicator_of_indepSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma indepFun_indicator_of_indepSet
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {s t : Set Ω}
-- given
  (h : IndepSet s t μ) :
-- imply
  IndepFun (s.indicator (1 : Ω → ℝ)) (t.indicator (1 : Ω → ℝ)) μ := by
-- proof
  rwa [IndepFun, IndepSet] at *
    (Kernel.indep_of_indep_of_le_right h (comap_indicator_one_le_generateFrom t))
    (comap_indicator_one_le_generateFrom s)

/--
[memLp_indicator_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma memLp_indicator_one
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {s : Set Ω}
-- given
  (hs : MeasurableSet s) :
-- imply
  MemLp (s.indicator (1 : Ω → ℝ)) 2 μ :=
-- proof
  memLp_indicator_const 2 hs 1 (Or.inr (measure_ne_top μ s))

/--
[indicator_one_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma indicator_one_sq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {s : Set Ω} :
-- imply
  s.indicator (1 : Ω → ℝ) ^ 2 = s.indicator 1 := by
-- proof
  ext ω; simp only [Pi.pow_apply, indicator, Pi.one_apply]; split_ifs <;> ring

/--
[variance_indicator_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma variance_indicator_le
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {s : Set Ω}
-- given
  (hs : MeasurableSet s) :
-- imply
  variance (s.indicator (1 : Ω → ℝ)) μ ≤ (μ s).toReal := by
-- proof
  rw [variance_eq_sub (memLp_indicator_one hs)]
  rw [indicator_one_sq, integral_indicator_one hs, measureReal_def]
  linarith [sq_nonneg ((μ s).toReal)]

/--
[integral_partialSumIndicators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma integral_partialSumIndicators
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {n : ℕ}
-- given
  (hA : ∀ i, MeasurableSet (A i)) :
-- imply
  ∫ ω, partialSumIndicators A n ω ∂μ = ∑ i ∈ Finset.range n, (μ (A i)).toReal := by
-- proof
  simp only [partialSumIndicators]
  rw [integral_finset_sum _ (fun i _ => (memLp_indicator_one (hA i)).integrable one_le_two)]
  congr 1 with i
  rw [integral_indicator_one (hA i), measureReal_def]

/--
[variance_partialSumIndicators_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma variance_partialSumIndicators_le
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {n : ℕ}
-- given
  (hA : ∀ i, MeasurableSet (A i))
  (hindep : Pairwise fun i j => IndepSet (A i) (A j) μ) :
-- imply
  variance (partialSumIndicators A n) μ ≤ integral μ (partialSumIndicators A n) := by
-- proof
  rw [partialSumIndicators_eq]
  have hmem : ∀ i ∈ Finset.range n, MemLp ((A i).indicator (1 : Ω → ℝ)) 2 μ :=
    fun i _ => memLp_indicator_one (hA i)
  have hindepFun : (↑(Finset.range n) : Set ℕ).Pairwise
    fun i j => IndepFun ((A i).indicator (1 : Ω → ℝ)) ((A j).indicator (1 : Ω → ℝ)) μ :=
    fun _ _ _ _ hij => indepFun_indicator_of_indepSet (hindep hij)
  rw [IndepFun.variance_sum hmem hindepFun]
  show _ ≤ ∫ ω, (∑ i ∈ Finset.range n, (A i).indicator (1 : Ω → ℝ)) ω ∂μ
  simp_rw [Finset.sum_apply]
  rw [integral_finset_sum _ (fun i hi => (hmem i hi).integrable one_le_two)]
  apply Finset.sum_le_sum
  intro i _
  rw [integral_indicator_one (hA i), measureReal_def]
  exact variance_indicator_le (hA i)

/--
[ES_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma ES_tendsto_atTop
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
-- given
  (hA : ∀ i, MeasurableSet (A i))
  (hsum : ∑' n, μ (A n) = ⊤) :
-- imply
  Filter.Tendsto (fun n => ∫ ω, partialSumIndicators A n ω ∂μ) Filter.atTop Filter.atTop := by
-- proof
  simp_rw [integral_partialSumIndicators A hA]
  have hnn : ∀ n, 0 ≤ (μ (A n)).toReal := fun _ => ENNReal.toReal_nonneg
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg hnn]
  intro h
  have h1 : ∑' n, ENNReal.ofReal ((μ (A n)).toReal) < ⊤ := h.tsum_ofReal_lt_top
  simp_rw [ENNReal.ofReal_toReal (measure_ne_top μ (A _))] at h1
  exact absurd hsum (ne_of_lt h1)

/--
[ES_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma ES_mono
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
-- given
  (hA : ∀ i, MeasurableSet (A i)) :
-- imply
  Monotone (fun n => ∫ ω, partialSumIndicators A n ω ∂μ) := by
-- proof
  intro m n hmn
  simp_rw [integral_partialSumIndicators A hA]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun _ _ _ => ENNReal.toReal_nonneg)

/--
[ES_step_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma ES_step_le_one
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {n : ℕ}
-- given
  (hA : ∀ i, MeasurableSet (A i)) :
-- imply
  ∫ ω, partialSumIndicators A (n + 1) ω ∂μ - ∫ ω, partialSumIndicators A n ω ∂μ ≤ 1 := by
-- proof
  simp_rw [integral_partialSumIndicators A hA, Finset.sum_range_succ]
  ring_nf
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one ▸ prob_le_one)

/--
[sllnSubseq_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma sllnSubseq_spec
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {k : ℕ}
-- given
  (hES_top : Filter.Tendsto (fun n => ∫ ω, partialSumIndicators A n ω ∂μ) Filter.atTop Filter.atTop) :
-- imply
  ((k : ℝ) + 1) ^ 2 ≤ ∫ ω, partialSumIndicators A (sllnSubseq hES_top k) ω ∂μ := by
-- proof
  classical
  exact Nat.find_spec
    ((hES_top.eventually (Filter.eventually_ge_atTop (((k : ℝ) + 1) ^ 2))).exists)

/--
[sllnSubseq_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma sllnSubseq_pos
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {k : ℕ}
-- given
  (hES_top : Filter.Tendsto (fun n => ∫ ω, partialSumIndicators A n ω ∂μ) Filter.atTop Filter.atTop) :
-- imply
  0 < sllnSubseq hES_top k := by
-- proof
  rw [Nat.pos_iff_ne_zero]
  intro h
  have h1 := sllnSubseq_spec hES_top k
  change sllnSubseq hES_top k = 0 at h
  rw [h] at h1
  have h2 : ∫ ω, partialSumIndicators A 0 ω ∂μ = 0 := by simp [partialSumIndicators]
  linarith [show 0 < ((k : ℝ) + 1) ^ 2 from by positivity]

/--
[sllnSubseq_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma sllnSubseq_strictMono
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
-- given
  (hA : ∀ i, MeasurableSet (A i))
  (hES_top : Filter.Tendsto (fun n => ∫ ω, partialSumIndicators A n ω ∂μ) Filter.atTop Filter.atTop) :
-- imply
  StrictMono (sllnSubseq hES_top) := by
-- proof
  classical
  intro k k' hkk'
  have hpos : 0 < sllnSubseq hES_top k := sllnSubseq_pos hES_top k
  obtain ⟨m, hm⟩ : ∃ m, sllnSubseq hES_top k = m + 1 :=
    ⟨sllnSubseq hES_top k - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hmin_m : ∫ ω, partialSumIndicators A m ω ∂μ < ((k : ℝ) + 1) ^ 2 :=
    not_le.mp (Nat.find_min _ (by omega : m < sllnSubseq hES_top k))
  have hub : ∫ ω, partialSumIndicators A (sllnSubseq hES_top k) ω ∂μ <
    ((k : ℝ) + 1) ^ 2 + 1 := by
    rw [hm]; linarith [ES_step_le_one (μ := μ) A hA m]
  have hthresh : ((k : ℝ) + 1) ^ 2 + 1 ≤ ((k' : ℝ) + 1) ^ 2 := by
    have : (k : ℝ) + 2 ≤ (k' : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkk' 1
    nlinarith
  have hlt : ∫ ω, partialSumIndicators A (sllnSubseq hES_top k) ω ∂μ <
    ((k' : ℝ) + 1) ^ 2 := by linarith
  by_contra hle
  push Not at hle
  have h_mono := ES_mono (μ := μ) A hA hle
  have h_spec := sllnSubseq_spec hES_top k'
  linarith

/--
[ES_sllnSubseq_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma ES_sllnSubseq_pos
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {k : ℕ}
-- given
  (hES_top : Filter.Tendsto (fun n => ∫ ω, partialSumIndicators A n ω ∂μ) Filter.atTop Filter.atTop) :
-- imply
  0 < ∫ ω, partialSumIndicators A (sllnSubseq hES_top k) ω ∂μ := by
-- proof
  have h := sllnSubseq_spec hES_top k
  have : 0 < ((k : ℝ) + 1) ^ 2 := by positivity
  linarith

/--
[memLp_partialSumIndicators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma memLp_partialSumIndicators
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {n : ℕ}
-- given
  (hA : ∀ i, MeasurableSet (A i)) :
-- imply
  MemLp (partialSumIndicators A n) 2 μ := by
-- proof
  rw [partialSumIndicators_eq]
  exact memLp_finset_sum' _ (fun i _ => memLp_indicator_one (hA i))

/--
[ae_tendsto_of_ae_eventually_abs_sub_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma ae_tendsto_of_ae_eventually_abs_sub_lt
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {f : ℕ → Ω → ℝ}
  {a : ℝ}
-- given
  (h : ∀ m : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ k in Filter.atTop, |f k ω - a| < 1 / ((m : ℝ) + 1)) :
-- imply
  ∀ᵐ ω ∂μ, Filter.Tendsto (fun k => f k ω) Filter.atTop (nhds a) := by
-- proof
  have h' : ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ᶠ k in Filter.atTop, |f k ω - a| < 1 / ((m : ℝ) + 1) := by
    rwa [ae_all_iff]
  filter_upwards [h'] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
  have hm_pos : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hm1 : 1 / ((m : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hm_pos]
    have := (div_lt_iff₀ hε).mp hm
    linarith
  obtain ⟨N, hN⟩ := (hω m).exists_forall_of_atTop
  exact ⟨N, fun n hn => lt_trans (by rw [Real.dist_eq]; exact hN n hn) hm1⟩

/--
[chebyshev_subseq_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma chebyshev_subseq_bound
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {ε : ℝ}
  {k : ℕ}
-- given
  (hA : ∀ i, MeasurableSet (A i))
  (hindep : Pairwise fun i j => IndepSet (A i) (A j) μ)
  (hES_top : Filter.Tendsto (fun n => ∫ ω, partialSumIndicators A n ω ∂μ) Filter.atTop Filter.atTop)
  (hε : 0 < ε) :
-- imply
  μ {ω | ε ≤ |partialSumIndicators A (sllnSubseq hES_top k) ω / (∫ ω', partialSumIndicators A (sllnSubseq hES_top k) ω' ∂μ) - 1|} ≤ ENNReal.ofReal (1 / (ε ^ 2 * ((k : ℝ) + 1) ^ 2)) := by
-- proof
  set n := sllnSubseq hES_top k with hn_def
  set ESn := ∫ ω', partialSumIndicators A n ω' ∂μ with hESn_def
  have hESn_pos : 0 < ESn := ES_sllnSubseq_pos hES_top k
  have hESn_sq : ((k : ℝ) + 1) ^ 2 ≤ ESn := sllnSubseq_spec hES_top k
  have hsub : {ω | ε ≤ |partialSumIndicators A n ω / ESn - 1|} ⊆
    {ω | ε * ESn ≤ |partialSumIndicators A n ω - ESn|} := by
    intro ω hω
    simp only [mem_setOf_eq] at hω ⊢
    have key : partialSumIndicators A n ω / ESn - 1 =
      (partialSumIndicators A n ω - ESn) / ESn := by
      field_simp
    rw [key, abs_div, abs_of_pos hESn_pos] at hω
    have h1 : ε ≤ |partialSumIndicators A n ω - ESn| / ESn := hω
    exact le_of_le_of_eq (mul_le_mul_of_nonneg_right h1 hESn_pos.le)
      (div_mul_cancel₀ _ (ne_of_gt hESn_pos))
  have hc_pos : 0 < ε * ESn := mul_pos hε hESn_pos
  have hmemLp : MemLp (partialSumIndicators A n) 2 μ := memLp_partialSumIndicators A hA n
  have hcheb := meas_ge_le_variance_div_sq hmemLp hc_pos
  have hvar := variance_partialSumIndicators_le A hA hindep n
  calc μ {ω | ε ≤ |partialSumIndicators A n ω / ESn - 1|}
    ≤ μ {ω | ε * ESn ≤ |partialSumIndicators A n ω -
      ∫ x, partialSumIndicators A n x ∂μ|} := by
      apply measure_mono hsub
    _ ≤ ENNReal.ofReal (variance (partialSumIndicators A n) μ / (ε * ESn) ^ 2) := hcheb
    _ ≤ ENNReal.ofReal (ESn / (ε * ESn) ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right hvar (by positivity)
    _ = ENNReal.ofReal (1 / (ε ^ 2 * ESn)) := by
      congr 1
      have hESn_ne : ESn ≠ 0 := ne_of_gt hESn_pos
      have hε_ne : ε ≠ 0 := ne_of_gt hε
      field_simp
    _ ≤ ENNReal.ofReal (1 / (ε ^ 2 * ((k : ℝ) + 1) ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hESn_sq (by positivity)

/--
[summable_chebyshev_subseq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma summable_chebyshev_subseq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {ε : ℝ}
-- given
  (hA : ∀ i, MeasurableSet (A i))
  (hindep : Pairwise fun i j => IndepSet (A i) (A j) μ)
  (hES_top : Filter.Tendsto (fun n => ∫ ω, partialSumIndicators A n ω ∂μ) Filter.atTop Filter.atTop)
  (hε : 0 < ε) :
-- imply
  ∑' k, μ {ω | ε ≤ |partialSumIndicators A (sllnSubseq hES_top k) ω / (∫ ω', partialSumIndicators A (sllnSubseq hES_top k) ω' ∂μ) - 1|} ≠ ⊤ := by
-- proof
  apply ne_top_of_le_ne_top
  · have : ∑' (k : ℕ), ENNReal.ofReal (1 / (ε ^ 2 * ((k : ℝ) + 1) ^ 2)) < ⊤ := by
    have hsumm : Summable (fun k : ℕ => 1 / (ε ^ 2 * ((k : ℝ) + 1) ^ 2)) := by
      have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
        have h2 := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num : 1 < 2)
        have heq : (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) =
          (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) ∘ (· + 1) := by
          ext n; simp only [Function.comp, one_div]; push_cast; ring
        rw [heq]
        exact h2.comp_injective (fun a b hab => by omega)
      exact (Summable.mul_left (1 / ε ^ 2) hshift).congr (fun k => by
        have hε2 : ε ^ 2 ≠ 0 := by positivity
        have hk : ((k : ℝ) + 1) ^ 2 ≠ 0 := by positivity
        field_simp)
    exact hsumm.tsum_ofReal_lt_top
    exact this.ne
  · exact ENNReal.tsum_le_tsum (fun k =>
    chebyshev_subseq_bound A hA hindep hES_top ε hε k)

/--
[partialSumIndicators_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma partialSumIndicators_mono
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {ω : Ω} :
-- imply
  Monotone (fun n => partialSumIndicators A n ω) := by
-- proof
  intro m n hmn
  simp only [partialSumIndicators]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
  intro i _ _
  exact Set.indicator_nonneg (fun _ _ => one_pos.le) ω

/--
[partialSumIndicators_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma partialSumIndicators_nonneg
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {n : ℕ}
  {ω : Ω} :
-- imply
  0 ≤ partialSumIndicators A n ω := by
-- proof
  simp only [partialSumIndicators]
  apply Finset.sum_nonneg
  intro i _
  exact Set.indicator_nonneg (fun _ _ => one_pos.le) ω

/--
[exists_bracket_of_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma exists_bracket_of_strictMono
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {φ : ℕ → ℕ}
  {n : ℕ}
-- given
  (hφ : StrictMono φ)
  (hn : φ 0 ≤ n) :
-- imply
  ∃ k, φ k ≤ n ∧ n < φ (k + 1) := by
-- proof
  have hid : ∀ k, k ≤ φ k := StrictMono.id_le hφ
  have hex : ∃ k, n < φ (k + 1) :=
    ⟨n, lt_of_lt_of_le (Nat.lt_succ_of_le le_rfl) (hid (n + 1))⟩
  set k := Nat.find hex with hk_def
  have hk_spec : n < φ (k + 1) := Nat.find_spec hex
  refine ⟨k, ?_, hk_spec⟩
  obtain hk0 | hk_pos := Nat.eq_zero_or_pos k
  · rw [hk0]; exact hn
  · have hk_pred : k - 1 < k := Nat.sub_lt hk_pos Nat.one_pos
    have hmm := Nat.find_min hex hk_pred
    push Not at hmm
    have hkk : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk_pos
    rwa [hkk] at hmm

/--
[ES_sllnSubseq_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma ES_sllnSubseq_upper_bound
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
  {k : ℕ}
-- given
  (hA : ∀ i, MeasurableSet (A i))
  (hES_top : Filter.Tendsto (fun n => ∫ ω, partialSumIndicators A n ω ∂μ) Filter.atTop Filter.atTop) :
-- imply
  ∫ ω, partialSumIndicators A (sllnSubseq hES_top k) ω ∂μ < ((k : ℝ) + 1) ^ 2 + 1 := by
-- proof
  classical
  have hpos : 0 < sllnSubseq hES_top k := sllnSubseq_pos hES_top k
  obtain ⟨m, hm⟩ : ∃ m, sllnSubseq hES_top k = m + 1 :=
    ⟨sllnSubseq hES_top k - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hmin_m : ∫ ω, partialSumIndicators A m ω ∂μ < ((k : ℝ) + 1) ^ 2 :=
    not_le.mp (Nat.find_min _ (by omega : m < sllnSubseq hES_top k))
  rw [hm]; linarith [ES_step_le_one (μ := μ) A hA m]

/--
[ES_subseq_ratio_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma ES_subseq_ratio_tendsto_one
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
-- given
  (hA : ∀ i, MeasurableSet (A i))
  (hES_top : Filter.Tendsto (fun n => ∫ ω, partialSumIndicators A n ω ∂μ) Filter.atTop Filter.atTop) :
-- imply
  Filter.Tendsto (fun k => (∫ ω, partialSumIndicators A (sllnSubseq hES_top (k + 1)) ω ∂μ) / (∫ ω, partialSumIndicators A (sllnSubseq hES_top k) ω ∂μ)) Filter.atTop (nhds 1) := by
-- proof
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (4 / ε)
  refine ⟨K, fun k hk => ?_⟩
  rw [Real.dist_eq]
  set a := ∫ ω, partialSumIndicators A (sllnSubseq hES_top (k + 1)) ω ∂μ
  set b := ∫ ω, partialSumIndicators A (sllnSubseq hES_top k) ω ∂μ
  have hb_pos : 0 < b := ES_sllnSubseq_pos hES_top k
  have ha_pos : 0 < a := ES_sllnSubseq_pos hES_top (k + 1)
  have hb_sq : ((k : ℝ) + 1) ^ 2 ≤ b := sllnSubseq_spec hES_top k
  have ha_ub : a < ((k : ℝ) + 1 + 1) ^ 2 + 1 := by
    have := ES_sllnSubseq_upper_bound hA hES_top (k + 1)
    push_cast at this; linarith
  have hab : b ≤ a := ES_mono (μ := μ) A hA (le_of_lt (sllnSubseq_strictMono hA hES_top (Nat.lt_succ_of_le le_rfl)))
  have h_ge_one : 1 ≤ a / b := le_div_iff₀ hb_pos |>.mpr (by linarith)
  rw [abs_of_nonneg (by linarith)]
  have h_step : a / b - 1 = (a - b) / b := by
    rw [div_sub_one (ne_of_gt hb_pos)]
  rw [h_step]
  have h_diff : a - b < 2 * (k : ℝ) + 4 := by
    have hb_lb := sllnSubseq_spec hES_top k
    have : a < ((k : ℝ) + 2) ^ 2 + 1 := by push_cast at ha_ub ⊢; linarith
    nlinarith
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  calc (a - b) / b ≤ (a - b) / ((k : ℝ) + 1) ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) hb_sq
    _ < (2 * (k : ℝ) + 4) / ((k : ℝ) + 1) ^ 2 :=
      div_lt_div_of_pos_right h_diff (by positivity)
    _ ≤ 4 / ((k : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2) hk1_pos]
      nlinarith [sq_nonneg ((k : ℝ) + 1)]
    _ < ε := by
      rw [div_lt_iff₀ hk1_pos]
      have hK1 : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hK2 : 4 < (K : ℝ) * ε := by rwa [div_lt_iff₀ hε] at hK
      nlinarith

/--
[pairwise_indep_slln](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PairwiseIndepSLLN.lean)
-/
@[path]
lemma pairwise_indep_slln
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {A : ℕ → Set Ω}
-- given
  (hA_meas : ∀ n, MeasurableSet (A n))
  (hA_indep : Pairwise fun i j => IndepSet (A i) (A j) μ)
  (hA_sum : ∑' n, μ (A n) = ⊤) :
-- imply
  ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => (∑ i ∈ Finset.range n, (A i).indicator (1 : Ω → ℝ) ω) / (∑ i ∈ Finset.range n, (μ (A i)).toReal)) Filter.atTop (nhds 1) := by
-- proof
  suffices h : ∀ᵐ ω ∂μ, Filter.Tendsto
    (fun n => partialSumIndicators A n ω /
      ∫ ω', partialSumIndicators A n ω' ∂μ)
    Filter.atTop (nhds 1) by
    filter_upwards [h] with ω hω
    simp_rw [integral_partialSumIndicators A hA_meas] at hω
    exact hω
  have hES_top := ES_tendsto_atTop A hA_meas hA_sum
  have hES_mono := ES_mono (μ := μ) A hA_meas
  set φ := sllnSubseq hES_top
  have hφ_strict : StrictMono φ := sllnSubseq_strictMono hA_meas hES_top
  have hES_φ_pos : ∀ k, 0 < ∫ ω', partialSumIndicators A (φ k) ω' ∂μ :=
    fun k => ES_sllnSubseq_pos hES_top k
  have hρ := ES_subseq_ratio_tendsto_one hA_meas hES_top
  have hφ_ae : ∀ᵐ ω ∂μ, Filter.Tendsto
    (fun k => partialSumIndicators A (φ k) ω /
      ∫ ω', partialSumIndicators A (φ k) ω' ∂μ)
    Filter.atTop (nhds 1) := by
    apply ae_tendsto_of_ae_eventually_abs_sub_lt
    intro m
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hfin := summable_chebyshev_subseq A hA_meas hA_indep hES_top _ hε
    filter_upwards [ae_eventually_notMem hfin] with ω hω
    exact hω.mono (fun k hk => not_le.mp hk)
  filter_upwards [hφ_ae] with ω hω_subseq
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := min (ε / 4) (1 / 2) with hδ_def
  have hδ_pos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_le_half : δ ≤ 1 / 2 := min_le_right _ _
  have hδ_le_ε4 : δ ≤ ε / 4 := min_le_left _ _
  obtain ⟨K₁, hK₁⟩ := (Metric.tendsto_atTop.mp hω_subseq) δ hδ_pos
  obtain ⟨K₂, hK₂⟩ := (Metric.tendsto_atTop.mp hρ) δ hδ_pos
  set K := max K₁ K₂
  refine ⟨φ K, fun n hn => ?_⟩
  have hn0 : φ 0 ≤ n := le_trans (hφ_strict.monotone (Nat.zero_le K)) hn
  obtain ⟨k, hk_lb, hk_ub⟩ := exists_bracket_of_strictMono φ hφ_strict n hn0
  have hk_ge : K ≤ k := by
    by_contra hlt; push Not at hlt
    exact absurd (lt_of_lt_of_le hk_ub (hφ_strict.monotone hlt)) (not_lt.mpr hn)
  have h_rk : |partialSumIndicators A (φ k) ω /
    (∫ ω', partialSumIndicators A (φ k) ω' ∂μ) - 1| < δ := by
    rw [← Real.dist_eq]; exact hK₁ k (le_trans (le_max_left _ _) hk_ge)
  have h_rk1 : |partialSumIndicators A (φ (k + 1)) ω /
    (∫ ω', partialSumIndicators A (φ (k + 1)) ω' ∂μ) - 1| < δ := by
    rw [← Real.dist_eq]; exact hK₁ (k + 1) (by omega)
  have h_ρk : |(∫ ω', partialSumIndicators A (φ (k + 1)) ω' ∂μ) /
    (∫ ω', partialSumIndicators A (φ k) ω' ∂μ) - 1| < δ := by
    rw [← Real.dist_eq]; exact hK₂ k (le_trans (le_max_right _ _) hk_ge)
  have hEφk := hES_φ_pos k
  have hEφk1 := hES_φ_pos (k + 1)
  have hEn : 0 < ∫ ω', partialSumIndicators A n ω' ∂μ :=
    lt_of_lt_of_le hEφk (hES_mono hk_lb)
  have hSn_lb := partialSumIndicators_mono A ω hk_lb
  have hSn_ub := partialSumIndicators_mono A ω (le_of_lt hk_ub)
  have hEn_lb : ∫ ω', partialSumIndicators A (φ k) ω' ∂μ ≤
    ∫ ω', partialSumIndicators A n ω' ∂μ := hES_mono hk_lb
  have hEn_ub : ∫ ω', partialSumIndicators A n ω' ∂μ ≤
    ∫ ω', partialSumIndicators A (φ (k + 1)) ω' ∂μ := hES_mono (le_of_lt hk_ub)
  have hSφk_nn := partialSumIndicators_nonneg A (φ k) ω
  have hSn_nn := partialSumIndicators_nonneg A n ω
  set r₀ := partialSumIndicators A (φ k) ω / (∫ ω', partialSumIndicators A (φ k) ω' ∂μ)
  set r₁ := partialSumIndicators A (φ (k + 1)) ω / (∫ ω', partialSumIndicators A (φ (k + 1)) ω' ∂μ)
  set ρ := (∫ ω', partialSumIndicators A (φ (k + 1)) ω' ∂μ) / (∫ ω', partialSumIndicators A (φ k) ω' ∂μ)
  have hρ_pos : 0 < ρ := div_pos hEφk1 hEφk
  have hub_eq : partialSumIndicators A (φ (k + 1)) ω /
    (∫ ω', partialSumIndicators A (φ k) ω' ∂μ) = r₁ * ρ := by
    simp only [r₁, ρ]; field_simp
  have hlb_eq : partialSumIndicators A (φ k) ω /
    (∫ ω', partialSumIndicators A (φ (k + 1)) ω' ∂μ) = r₀ / ρ := by
    simp only [r₀, ρ]; field_simp
  have h_lower : r₀ / ρ ≤
    partialSumIndicators A n ω / (∫ ω', partialSumIndicators A n ω' ∂μ) := by
    rw [← hlb_eq]
    calc partialSumIndicators A (φ k) ω / (∫ ω', partialSumIndicators A (φ (k + 1)) ω' ∂μ)
      ≤ partialSumIndicators A (φ k) ω / (∫ ω', partialSumIndicators A n ω' ∂μ) :=
        div_le_div_of_nonneg_left hSφk_nn hEn hEn_ub
      _ ≤ partialSumIndicators A n ω / (∫ ω', partialSumIndicators A n ω' ∂μ) :=
        div_le_div_of_nonneg_right hSn_lb hEn.le
  have h_upper : partialSumIndicators A n ω /
    (∫ ω', partialSumIndicators A n ω' ∂μ) ≤ r₁ * ρ := by
    rw [← hub_eq]
    calc partialSumIndicators A n ω / (∫ ω', partialSumIndicators A n ω' ∂μ)
      ≤ partialSumIndicators A n ω / (∫ ω', partialSumIndicators A (φ k) ω' ∂μ) :=
        div_le_div_of_nonneg_left hSn_nn hEφk hEn_lb
      _ ≤ partialSumIndicators A (φ (k + 1)) ω / (∫ ω', partialSumIndicators A (φ k) ω' ∂μ) :=
        div_le_div_of_nonneg_right hSn_ub hEφk.le
  rw [Real.dist_eq]
  have hub_bound : |r₁ * ρ - 1| < ε := by
    have heq : r₁ * ρ - 1 = (r₁ - 1) * (ρ - 1) + (r₁ - 1) + (ρ - 1) := by ring
    rw [heq]
    have hδ_sq_bound : δ ^ 2 + 2 * δ < ε := by nlinarith [sq_nonneg (δ - 1/2)]
    calc |(r₁ - 1) * (ρ - 1) + (r₁ - 1) + (ρ - 1)|
      ≤ |(r₁ - 1) * (ρ - 1) + (r₁ - 1)| + |ρ - 1| := abs_add_le _ _
      _ ≤ (|(r₁ - 1) * (ρ - 1)| + |r₁ - 1|) + |ρ - 1| := by
        gcongr; exact abs_add_le _ _
      _ = |r₁ - 1| * |ρ - 1| + |r₁ - 1| + |ρ - 1| := by rw [abs_mul]
      _ < δ * δ + δ + δ := by
        have h1 : |r₁ - 1| * |ρ - 1| < δ * δ :=
          mul_lt_mul'' h_rk1 h_ρk (abs_nonneg _) (abs_nonneg _)
        linarith
      _ = δ ^ 2 + 2 * δ := by ring
      _ < ε := hδ_sq_bound
  have hlb_bound : |r₀ / ρ - 1| < ε := by
    have hρ_lb : 1 / 2 < ρ := by
      have := (abs_sub_lt_iff.mp h_ρk).2; linarith
    have h_eq : r₀ / ρ - 1 = (r₀ - ρ) / ρ := by
      rw [div_sub_one (ne_of_gt hρ_pos)]
    rw [h_eq, abs_div, abs_of_pos hρ_pos]
    have h_num : |r₀ - ρ| < 2 * δ := by
      have h1 : |r₀ - ρ| = |(r₀ - 1) - (ρ - 1)| := by ring_nf
      rw [h1]; exact (abs_sub _ _).trans_lt (by linarith)
    calc |r₀ - ρ| / ρ < 2 * δ / ρ :=
      div_lt_div_of_pos_right h_num hρ_pos
      _ ≤ 2 * δ / (1 / 2) :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) (le_of_lt hρ_lb)
      _ = 4 * δ := by ring
      _ ≤ ε := by linarith
  set q := partialSumIndicators A n ω / (∫ ω', partialSumIndicators A n ω' ∂μ) with hq_def
  have hq_lb : 1 - ε < q := by
    have := (abs_sub_lt_iff.mp hlb_bound).2
    linarith
  have hq_ub : q < 1 + ε := by
    have := (abs_sub_lt_iff.mp hub_bound).1
    linarith
  rw [abs_sub_lt_iff]; exact ⟨by linarith, by linarith⟩


-- created on 2026-10-23
