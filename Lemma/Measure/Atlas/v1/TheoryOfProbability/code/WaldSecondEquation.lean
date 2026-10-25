import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfProbability.code.WaldSecondEquation
open MeasureTheory ProbabilityTheory Finset ENNReal Filter


/--
[wald_diagonal_terms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldSecondEquation.lean)
-/
@[path]
lemma wald_diagonal_terms
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}
  {f : Filtration ℕ m}
  {T : Ω → ℕ}
-- given
  (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
  (hX_ind : iIndepFun (β := fun _ => ℝ) X μ)
  (_hX_int : Integrable (X 0) μ)
  (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
  (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
  (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
  (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
-- imply
  ∫ ω, (∑ i ∈ Finset.range (T ω), (X i ω) ^ 2) ∂μ = (∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, (T ω : ℝ) ∂μ) := by
-- proof
  let Y : ℕ → Ω → ℝ := fun i ω => (X i ω) ^ 2
  show ∫ ω, (∑ i ∈ Finset.range (T ω), Y i ω) ∂μ =
    (∫ ω, Y 0 ω ∂μ) * (∫ ω, (T ω : ℝ) ∂μ)
  have sq_meas : Measurable (fun x : ℝ => x ^ 2) := measurable_id.pow_const 2
  have hY_iid : ∀ i j, IdentDistrib (Y i) (Y j) μ μ :=
    fun i j => (hX_iid i j).comp sq_meas
  have hY_ind : iIndepFun (β := fun _ => ℝ) Y μ :=
    hX_ind.comp (fun _ => fun x => x ^ 2) (fun _ => sq_meas)
  have hY_int : Integrable (Y 0) μ := hX_sq_int
  have hYf : ∀ k, Indep (MeasurableSpace.comap (Y k) inferInstance) (f k) μ := by
    intro k
    exact indep_of_indep_of_le_left (hXf k)
      (fun s ⟨t, ht, hts⟩ => ⟨(fun x => x ^ 2) ⁻¹' t, sq_meas ht, hts⟩)
  exact wald_equation hY_iid hY_ind hY_int hT hYf hT_int

/--
[cross_pair_integral_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldSecondEquation.lean)
-/
@[path]
lemma cross_pair_integral_zero
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}
  {f : Filtration ℕ m}
  {T : Ω → ℕ}
  {j i : ℕ}
-- given
  (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
  (hX_int : Integrable (X 0) μ)
  (hmean : ∫ ω, X 0 ω ∂μ = 0)
  (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
  (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
  (hadapt : ∀ j k, j < k → @Measurable Ω ℝ (f k) inferInstance (X j))
  (hji : j < i) :
-- imply
  ∫ ω, (if i < T ω then X j ω * X i ω else 0) ∂μ = 0 := by
-- proof
  have h_eq : (fun ω => if i < T ω then X j ω * X i ω else 0) =
    fun ω => (X j ω * Set.indicator {ω | i < T ω} (fun _ => (1 : ℝ)) ω) * X i ω := by
    ext ω; simp only [Set.indicator, Set.mem_setOf_eq]; split_ifs <;> ring
  rw [h_eq]
  set g : Ω → ℝ := fun ω => X j ω * Set.indicator {ω | i < T ω} (fun _ => (1 : ℝ)) ω
  have hind_meas : @MeasurableSet Ω (f i) {ω | i < T ω} := by
    have : {ω : Ω | i < T ω} = {ω : Ω | (i : WithTop ℕ) < (T ω : WithTop ℕ)} := by
      ext ω; simp
    rw [this]; exact hT.measurableSet_gt i
  have hg_meas : @Measurable Ω ℝ (f i) inferInstance g :=
    (hadapt j i hji).mul (@Measurable.indicator Ω ℝ {ω | i < T ω} (fun _ => (1 : ℝ))
      (f i) inferInstance _ (@measurable_const ℝ Ω inferInstance (f i) (a := 1)) hind_meas)
  have hindep : IndepFun (X i) g μ := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (hXf i)
      (MeasurableSpace.comap_le_iff_le_map.mpr hg_meas.le_map)
  have hmean_i : ∫ ω, X i ω ∂μ = 0 := by rw [(hX_iid i 0).integral_eq]; exact hmean
  rw [hindep.symm.integral_fun_mul_eq_mul_integral
    (hg_meas.mono (f.le i) le_rfl).aestronglyMeasurable
    ((hX_iid i 0).integrable_iff.mpr hX_int).aestronglyMeasurable, hmean_i, mul_zero]

/--
[wald_cross_terms_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldSecondEquation.lean)
-/
@[path]
lemma wald_cross_terms_zero
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
  (hmean : ∫ ω, X 0 ω ∂μ = 0)
  (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
  (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
  (hadapt : ∀ j k, j < k → @Measurable Ω ℝ (f k) inferInstance (X j))
  (haesm : ∀ n, AEStronglyMeasurable (fun ω => if n < T ω then ∑ j ∈ Finset.range n, X j ω * X n ω else 0) μ)
  (hsumm : ∑' n, ∫⁻ ω, ‖(if n < T ω then ∑ j ∈ Finset.range n, X j ω * X n ω else 0)‖ₑ ∂μ ≠ ⊤) :
-- imply
  ∫ ω, (∑ i ∈ Finset.range (T ω), ∑ j ∈ Finset.range i, X j ω * X i ω) ∂μ = 0 := by
-- proof
  have h_eq : (fun ω => ∑ i ∈ Finset.range (T ω), ∑ j ∈ Finset.range i,
    X j ω * X i ω) =
    (fun ω => ∑' i, if i < T ω then ∑ j ∈ Finset.range i, X j ω * X i ω else 0) := by
    ext ω; exact sum_range_eq_tsum_ite _ _
  rw [h_eq]
  rw [integral_tsum haesm hsumm]
  have each_zero : ∀ i, ∫ ω, (if i < T ω then ∑ j ∈ Finset.range i,
    X j ω * X i ω else 0) ∂μ = 0 := by
    intro i
    have h_dist : (fun ω => if i < T ω then ∑ j ∈ Finset.range i,
      X j ω * X i ω else 0) =
      (fun ω => ∑ j ∈ Finset.range i, if i < T ω then X j ω * X i ω else 0) := by
      ext ω; split_ifs <;> simp
    rw [h_dist, integral_finset_sum]
    · apply Finset.sum_eq_zero; intro j hj
      exact cross_pair_integral_zero hX_iid hX_int hmean hT hXf hadapt j i (Finset.mem_range.mp hj)
    · intro j hj
      have hji : j < i := Finset.mem_range.mp hj
      have hj_int : Integrable (X j) μ := (hX_iid j 0).integrable_iff.mpr hX_int
      have hi_int : Integrable (X i) μ := (hX_iid i 0).integrable_iff.mpr hX_int
      have hindep := hX_ind.indepFun (Nat.ne_of_lt hji)
      have hprod : Integrable (fun ω => X j ω * X i ω) μ := by
        show Integrable (X j * X i) μ; exact hindep.integrable_mul hj_int hi_int
      have h_eq : (fun ω => if i < T ω then X j ω * X i ω else 0) =
        Set.indicator {ω | i < T ω} (fun ω => X j ω * X i ω) := by
        ext ω; simp [Set.indicator, Set.mem_setOf_eq]
      rw [h_eq]
      exact hprod.indicator ((measurable_of_isStoppingTime hT) (measurableSet_Ioi (a := i)))
  simp only [each_zero, tsum_zero]

/--
[sum_sq_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldSecondEquation.lean)
-/
@[path]
lemma sum_sq_expansion
  {n : ℕ}
  {f : ℕ → ℝ} :
-- imply
  (∑ i ∈ Finset.range n, f i) ^ 2 = ∑ i ∈ Finset.range n, (f i) ^ 2 + 2 * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, f j * f i := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]; rw [add_sq', ih]
    have h1 : (2 * ∑ i ∈ Finset.range n, f i) * f n =
      2 * (∑ j ∈ Finset.range n, f j * f n) := by
      rw [mul_assoc]; congr 1; exact Finset.sum_mul (Finset.range n) f (f n)
    rw [h1]; linarith

/--
[integrable_stopped_sum_sq_diag](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/WaldSecondEquation.lean)
-/
@[path]
lemma integrable_stopped_sum_sq_diag
  {m : MeasurableSpace Ω}
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}
  {f : Filtration ℕ m}
  {T : Ω → ℕ}
-- given
  (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
  (hX_ind : iIndepFun (β := fun _ => ℝ) X μ)
  (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
  (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
  (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
  (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
-- imply
  Integrable (fun ω => ∑ i ∈ Finset.range (T ω), (X i ω) ^ 2) μ := by
-- proof
  let Y : ℕ → Ω → ℝ := fun i ω => (X i ω) ^ 2
  have sq_meas : Measurable (fun x : ℝ => x ^ 2) := measurable_id.pow_const 2
  have hY_iid : ∀ i j, IdentDistrib (Y i) (Y j) μ μ :=
    fun i j => (hX_iid i j).comp sq_meas
  have hY_ind : iIndepFun (β := fun _ => ℝ) Y μ :=
    hX_ind.comp (fun _ => fun x => x ^ 2) (fun _ => sq_meas)
  have hY_int : Integrable (Y 0) μ := hX_sq_int
  have hYf : ∀ k, Indep (MeasurableSpace.comap (Y k) inferInstance) (f k) μ := by
    intro k
    exact indep_of_indep_of_le_left (hXf k)
      (fun s ⟨t, ht, hts⟩ => ⟨(fun x => x ^ 2) ⁻¹' t, sq_meas ht, hts⟩)
  simp_rw [sum_range_eq_tsum_ite (fun i => (X i _) ^ 2) (T _)]
  have hg : ∀ i, AEStronglyMeasurable (fun ω => if i < T ω then Y i ω else 0) μ :=
    fun n => aesm_summand hY_iid hY_int (measurable_of_isStoppingTime hT) n
  have hg' : ∑' i, ∫⁻ a, ‖(if i < T a then Y i a else 0)‖ₑ ∂μ ≠ ⊤ :=
    summability_condition hY_ind hY_int hY_iid hT hYf hT_int
  exact ⟨(aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
    (f := fun N a => ∑ i ∈ Finset.range N, if i < T a then Y i a else 0)
    (fun N => by
      change AEStronglyMeasurable (fun a => ∑ i ∈ Finset.range N, if i < T a then Y i a else 0) μ
      have : (fun a => ∑ i ∈ Finset.range N, if i < T a then Y i a else 0) =
        ∑ i ∈ Finset.range N, (fun ω => if i < T ω then Y i ω else 0) := by
        ext a; simp [Finset.sum_apply]
      rw [this]
      exact Finset.aestronglyMeasurable_sum _ (fun i _ => hg i))
    (by
      have hg'' : ∀ i, AEMeasurable (fun x => ‖(if i < T x then Y i x else 0)‖ₑ) μ :=
        fun i => (hg i).enorm
      have hlt : ∫⁻ a, ∑' i, ‖(if i < T a then Y i a else 0)‖ₑ ∂μ ≠ ⊤ := by
        rwa [lintegral_tsum hg'']
      filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hg'') hlt] with a ha
      have hsumm : Summable (fun n => if n < T a then Y n a else 0) := by
        have hn : Summable (fun n => ‖if n < T a then Y n a else 0‖) := by
          have : (fun n => ‖if n < T a then Y n a else 0‖) =
            (fun n => (‖if n < T a then Y n a else 0‖₊ : ℝ)) := by ext; simp
          rw [this]
          exact NNReal.summable_coe.mpr ((ENNReal.tsum_coe_ne_top_iff_summable).mp
            (by simp only [enorm_eq_nnnorm] at ha; exact ha.ne))
        exact hn.of_norm
      exact hsumm.hasSum.tendsto_sum_nat)),
    by
      rw [hasFiniteIntegral_iff_enorm]
      have hg'' : ∀ i, AEMeasurable (fun x => ‖(if i < T x then Y i x else 0)‖ₑ) μ :=
        fun i => (hg i).enorm
      calc ∫⁻ a, ‖∑' i, if i < T a then Y i a else 0‖ₑ ∂μ
        ≤ ∫⁻ a, ∑' i, ‖(if i < T a then Y i a else 0)‖ₑ ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hg'')
            (by rwa [lintegral_tsum hg''])] with a ha
          simp only [enorm_eq_nnnorm]
          have hsumm : Summable (fun n => ‖if n < T a then Y n a else 0‖₊) := by
            exact (ENNReal.tsum_coe_ne_top_iff_summable).mp
              (by simp only [enorm_eq_nnnorm] at ha; exact ha.ne)
          exact (ENNReal.coe_le_coe.mpr (nnnorm_tsum_le hsumm)).trans
            (ENNReal.coe_tsum hsumm ▸ le_refl _)
        _ = ∑' i, ∫⁻ a, ‖(if i < T a then Y i a else 0)‖ₑ ∂μ := lintegral_tsum hg''
        _ < ⊤ := lt_top_iff_ne_top.mpr hg'⟩


-- created on 2026-10-23
