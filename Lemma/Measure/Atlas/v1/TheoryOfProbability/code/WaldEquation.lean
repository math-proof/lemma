import Mathlib
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset ENNReal


/--
[measurable_of_isStoppingTime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldEquation.lean)
-/
@[path]
lemma measurable_of_isStoppingTime
  {m : MeasurableSpace Ω}
  {f : Filtration ℕ m}
  {T : Ω → ℕ}
-- given
  (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ))) :
-- imply
  Measurable T := by
-- proof
  apply measurable_to_nat
  intro ω
  exact (f.le (T ω)) _ (by convert hT.measurableSet_eq (T ω) using 1; ext x; simp)

/--
[tsum_measure_gt_eq_lintegral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldEquation.lean)
-/
@[path]
lemma tsum_measure_gt_eq_lintegral
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  {T : Ω → ℕ}
-- given
  (hT_meas : Measurable T) :
-- imply
  ∑' i, μ {ω | i < T ω} = ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ := by
-- proof
  have hmeas : ∀ i, MeasurableSet {ω : Ω | i < T ω} := fun i => hT_meas measurableSet_Ioi
  have key : ∀ ω, (T ω : ℝ≥0∞) =
    ∑' i, Set.indicator {ω | i < T ω} (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω; simp only [Set.indicator, Set.mem_setOf_eq]
    rw [tsum_eq_sum (s := range (T ω))]
    · rw [Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx)),
      Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range]
    · intro i hi; exact if_neg (Finset.mem_range.not.mp hi)
  calc ∑' i, μ {ω | i < T ω}
    = ∑' i, ∫⁻ a, Set.indicator {ω | i < T ω} (fun _ => 1) a ∂μ := by
      congr 1; ext i; rw [lintegral_indicator (hmeas i), setLIntegral_one]
    _ = ∫⁻ ω, ∑' i, Set.indicator {ω | i < T ω} (fun _ => 1) ω ∂μ := by
      rw [lintegral_tsum (fun i => (measurable_const.indicator (hmeas i)).aemeasurable)]
    _ = ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ := by congr 1; ext ω; exact (key ω).symm

/--
[nat_eq_tsum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldEquation.lean)
-/
@[path]
lemma nat_eq_tsum_indicator
  {k : ℕ} :
-- imply
  (k : ℝ) = ∑' n, (if n < k then (1 : ℝ) else 0) := by
-- proof
  rw [tsum_eq_sum (s := range k)]
  · rw [Finset.sum_congr rfl (fun x hx => if_pos (Finset.mem_range.mp hx)),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · intro i hi; exact if_neg (Finset.mem_range.not.mp hi)

/--
[integral_nat_eq_tsum_prob](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldEquation.lean)
-/
@[path]
lemma integral_nat_eq_tsum_prob
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {T : Ω → ℕ}
-- given
  (hT_meas : Measurable T)
  (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
-- imply
  ∫ ω, (T ω : ℝ) ∂μ = ∑' n, (μ {ω | n < T ω}).toReal := by
-- proof
  have heq : (fun ω => (T ω : ℝ)) = fun ω => ∑' n, (if n < T ω then (1 : ℝ) else 0) := by
    ext ω; exact nat_eq_tsum_indicator (T ω)
  rw [heq]
  have hind : ∀ n, (fun ω => if n < T ω then (1 : ℝ) else 0) =
    Set.indicator {ω | n < T ω} (fun _ => 1) := by
    intro n; ext ω; simp [Set.indicator, Set.mem_setOf_eq]
  have hmeas : ∀ n, MeasurableSet {ω : Ω | n < T ω} := fun n => hT_meas measurableSet_Ioi
  rw [integral_tsum]
  · congr 1; ext n
    rw [hind n, integral_indicator_const _ (hmeas n), smul_eq_mul, mul_one, Measure.real]
  · intro n; rw [hind n]; exact aestronglyMeasurable_const.indicator (hmeas n)
  · have h1 : ∀ i a, ‖if i < T a then (1:ℝ) else 0‖ₑ =
    Set.indicator {ω | i < T ω} (fun _ => (1 : ℝ≥0∞)) a := by
    intro i a; simp only [Set.indicator, Set.mem_setOf_eq]; split_ifs with h <;> simp
    simp_rw [h1, lintegral_indicator (hmeas _), setLIntegral_one,
      tsum_measure_gt_eq_lintegral hT_meas]
    have hfi : ∫⁻ ω, ‖(T ω : ℝ)‖ₑ ∂μ < ⊤ := hT_int.2
    rw [show (fun ω => ‖(T ω : ℝ)‖ₑ) = (fun ω => (T ω : ℝ≥0∞)) from ?_] at hfi
    · exact hfi.ne
    · ext ω; simp [enorm]

/--
[sum_range_eq_tsum_ite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldEquation.lean)
-/
@[path]
lemma sum_range_eq_tsum_ite
  {f : ℕ → ℝ}
  {n : ℕ} :
-- imply
  ∑ i ∈ range n, f i = ∑' i, (if i < n then f i else 0) := by
-- proof
  rw [tsum_eq_sum (s := range n)]
  · exact Finset.sum_congr rfl (fun x hx => by simp [Finset.mem_range.mp hx])
  · intro i hi; exact if_neg (Finset.mem_range.not.mp hi)

/--
[indepFun_indicator_of_indep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldEquation.lean)
-/
@[path]
lemma indepFun_indicator_of_indep
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  {g : Ω → ℝ}
  {m' : MeasurableSpace Ω}
  {A : Set Ω}
-- given
  (hindep : Indep (MeasurableSpace.comap g inferInstance) m' μ)
  (hA : @MeasurableSet Ω m' A) :
-- imply
  IndepFun g (Set.indicator A (fun _ => (1 : ℝ))) μ := by
-- proof
  rw [IndepFun_iff_Indep]
  apply indep_of_indep_of_le_right hindep
  intro s hs
  obtain ⟨t, _, rfl⟩ := hs
  by_cases h1 : (1 : ℝ) ∈ t <;> by_cases h0 : (0 : ℝ) ∈ t
  · convert @MeasurableSet.univ Ω m'
    ext ω; simp [Set.indicator]; split_ifs <;> simp [*]
  · convert hA
    ext ω; simp [Set.indicator]; constructor
    · intro h; split_ifs at h with hmem <;> [exact hmem; exact absurd h h0]
    · intro hmem; simp [hmem, h1]
  · convert hA.compl
    ext ω; simp [Set.indicator]; constructor
    · intro h; split_ifs at h with hmem <;> [exact absurd h h1; exact hmem]
    · intro hmem; simp [show ¬(ω ∈ A) from hmem, h0]
  · convert @MeasurableSet.empty Ω m'
    ext ω; simp [Set.indicator]; split_ifs <;> simp [*]

/--
[indep_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldEquation.lean)
-/
@[path]
lemma indep_factor
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}
  {f : Filtration ℕ m}
  {T : Ω → ℕ}
  {n : ℕ}
-- given
  (hX_int : Integrable (X 0) μ)
  (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
  (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
  (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ) :
-- imply
  ∫ ω, (if n < T ω then X n ω else 0) ∂μ = (∫ ω, X n ω ∂μ) * (μ {ω | n < T ω}).toReal := by
-- proof
  have hS : MeasurableSet {ω : Ω | n < T ω} := by
    have hT_meas : Measurable T := measurable_of_isStoppingTime hT
    exact hT_meas measurableSet_Ioi
  have heq_ind : (fun ω => if n < T ω then X n ω else 0) =
    fun ω => X n ω * Set.indicator {ω | n < T ω} (fun _ => (1 : ℝ)) ω := by
    ext ω; simp only [Set.indicator, Set.mem_setOf_eq]; split_ifs with h <;> ring
  rw [heq_ind]
  have hindep : IndepFun (X n) (Set.indicator {ω | n < T ω} (fun _ => (1 : ℝ))) μ := by
    apply indepFun_indicator_of_indep (hXf n)
    have key : {ω : Ω | n < T ω} = {ω | (fun ω => (T ω : WithTop ℕ)) ω ≤ ↑n}ᶜ := by
      ext ω; simp [not_le]
    rw [key]
    exact (hT n).compl
  have hXn_aesm : AEStronglyMeasurable (X n) μ :=
    (hX_iid n 0).aestronglyMeasurable_iff.mpr hX_int.aestronglyMeasurable
  have hind_aesm : AEStronglyMeasurable (Set.indicator {ω | n < T ω} (fun _ => (1 : ℝ))) μ :=
    aestronglyMeasurable_const.indicator hS
  rw [hindep.integral_fun_mul_eq_mul_integral hXn_aesm hind_aesm]
  congr 1
  rw [integral_indicator_const _ hS, smul_eq_mul, mul_one]
  rfl

/--
[lintegral_enorm_indicator_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldEquation.lean)
-/
@[path]
lemma lintegral_enorm_indicator_le
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}
  {f : Filtration ℕ m}
  {T : Ω → ℕ}
  {n : ℕ}
-- given
  (hX_ind : iIndepFun (β := fun _ => ℝ) X μ)
  (hX_int : Integrable (X 0) μ)
  (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
  (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
  (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
  (hT_meas : Measurable T) :
-- imply
  ∫⁻ a in {ω | n < T ω}, ‖X n a‖ₑ ∂μ ≤ (∫⁻ a, ‖X 0 a‖ₑ ∂μ) * μ {ω | n < T ω} := by
-- proof
  simp_rw [show ∀ (g : ℕ → Ω → ℝ) (k : ℕ) (a : Ω), ‖g k a‖ₑ = .ofReal ‖g k a‖ from
    fun g k a => by rw [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]]
  have hind_norm := hX_ind.comp (fun (_ : ℕ) => (‖·‖ : ℝ → ℝ)) (fun _ => measurable_norm)
  have hint_norm : Integrable (fun ω => ‖X 0 ω‖) μ := hX_int.norm
  have hiid_norm : ∀ i j, IdentDistrib (fun ω => ‖X i ω‖) (fun ω => ‖X j ω‖) μ μ :=
    fun i j => (hX_iid i j).comp measurable_norm
  have hXf_norm : ∀ k, Indep (MeasurableSpace.comap (fun ω => ‖X k ω‖) inferInstance) (f k) μ := by
    intro k
    exact indep_of_indep_of_le_left (hXf k)
      (fun s ⟨t, ht, hts⟩ => ⟨(‖·‖) ⁻¹' t, measurable_norm ht, hts⟩)
  have hfactor := indep_factor hint_norm hiid_norm hT hXf_norm n
  have hmeas_set : MeasurableSet {ω : Ω | n < T ω} := hT_meas measurableSet_Ioi
  rw [show (fun ω => if n < T ω then ‖X n ω‖ else 0) =
    Set.indicator {ω | n < T ω} (fun ω => ‖X n ω‖) from by
      ext ω; simp [Set.indicator, Set.mem_setOf_eq],
    integral_indicator hmeas_set] at hfactor
  rw [(hiid_norm n 0).integral_eq] at hfactor
  have hXn_int : Integrable (X n) μ := (hX_iid n 0).integrable_iff.mpr hX_int
  rw [← ofReal_integral_eq_lintegral_ofReal (hXn_int.norm.restrict)
    (ae_of_all _ (fun _ => norm_nonneg _))]
  rw [← ofReal_integral_eq_lintegral_ofReal hint_norm
    (ae_of_all _ (fun _ => norm_nonneg _))]
  rw [hfactor]
  rw [ENNReal.ofReal_mul (integral_nonneg (fun ω => norm_nonneg _))]
  gcongr
  exact ofReal_toReal_le

/--
[summability_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldEquation.lean)
-/
@[path]
lemma summability_condition
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}
  {f : Filtration ℕ m}
  {T : Ω → ℕ}
-- given
  (hX_ind : iIndepFun (β := fun _ => ℝ) X μ)
  (hX_int : Integrable (X 0) μ)
  (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
  (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
  (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
  (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
-- imply
  ∑' (n : ℕ), ∫⁻ (a : Ω), ‖(if n < T a then X n a else 0)‖ₑ ∂μ ≠ ⊤ := by
-- proof
  have hT_meas : Measurable T := measurable_of_isStoppingTime hT
  have h_rewrite : ∀ n a, ‖(if n < T a then X n a else 0)‖ₑ =
    Set.indicator {ω | n < T ω} (fun ω => ‖X n ω‖ₑ) a := by
    intro n a; simp only [Set.indicator, Set.mem_setOf_eq]
    split_ifs with h <;> simp [enorm]
  simp_rw [h_rewrite]
  have hmeas : ∀ n, MeasurableSet {ω : Ω | n < T ω} := fun n => hT_meas measurableSet_Ioi
  simp_rw [lintegral_indicator (hmeas _)]
  have key := fun n => lintegral_enorm_indicator_le hX_ind hX_int hX_iid hT hXf hT_meas n
  have hbound_ne_top : ∑' n, (∫⁻ a, ‖X 0 a‖ₑ ∂μ) * μ {ω | n < T ω} ≠ ⊤ := by
    rw [ENNReal.tsum_mul_left]
    apply ENNReal.mul_ne_top
    · exact hX_int.2.ne
    · rw [tsum_measure_gt_eq_lintegral hT_meas]
      have hfi : ∫⁻ ω, ‖(T ω : ℝ)‖ₑ ∂μ < ⊤ := hT_int.2
      rw [show (fun ω => ‖(T ω : ℝ)‖ₑ) = (fun ω => (T ω : ℝ≥0∞)) from by ext ω; simp [enorm]]
        at hfi
      exact hfi.ne
  exact ne_top_of_le_ne_top hbound_ne_top (ENNReal.tsum_le_tsum key)

/--
[aesm_summand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldEquation.lean)
-/
@[path]
lemma aesm_summand
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  {X : ℕ → Ω → ℝ}
  {T : Ω → ℕ}
  {n : ℕ}
-- given
  (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
  (hX_int : Integrable (X 0) μ)
  (hT_meas : Measurable T) :
-- imply
  AEStronglyMeasurable (fun ω => if n < T ω then X n ω else 0) μ := by
-- proof
  have hXn_aesm : AEStronglyMeasurable (X n) μ :=
    (hX_iid n 0).aestronglyMeasurable_iff.mpr hX_int.aestronglyMeasurable
  have hset : MeasurableSet {ω : Ω | n < T ω} := hT_meas measurableSet_Ioi
  have heq : (fun ω => if n < T ω then X n ω else 0) = Set.indicator {ω | n < T ω} (X n) := by
    ext ω; simp [Set.indicator, Set.mem_setOf_eq]
  rw [heq]
  exact hXn_aesm.indicator hset

/--
[wald_equation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldEquation.lean)
-/
@[path]
lemma wald_equation
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}
  {f : Filtration ℕ m}
  {T : Ω → ℕ}
-- given
  (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
  (hX_ind : iIndepFun (β := fun _ => ℝ) X μ)
  (hX_int : Integrable (X 0) μ)
  (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
  (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
  (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
-- imply
  ∫ ω, (∑ i ∈ Finset.range (T ω), X i ω) ∂μ = (∫ ω, X 0 ω ∂μ) * (∫ ω, (T ω : ℝ) ∂μ) := by
-- proof
  have hT_meas : Measurable T := measurable_of_isStoppingTime hT
  simp_rw [sum_range_eq_tsum_ite (fun i => X i _) (T _)]
  rw [integral_tsum
    (fun n => aesm_summand hX_iid hX_int hT_meas n)
    (summability_condition hX_ind hX_int hX_iid hT hXf hT_int)]
  simp_rw [indep_factor hX_int hX_iid hT hXf]
  simp_rw [(hX_iid _ 0).integral_eq]
  rw [tsum_mul_left]
  congr 1
  exact (integral_nat_eq_tsum_prob hT_meas hT_int).symm


-- created on 2026-10-23
