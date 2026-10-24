import Mathlib
import sympy.Basic
open MeasureTheory
open scoped ComplexConjugate
open Filter
open scoped Topology
open Set


noncomputable def avgW (ρ : ℝ → ℝ) (u : ℝ → ℂ) (δ t : ℝ) : ℂ := ∫ w, u (t - δ * w) * (ρ w : ℂ)

private lemma avgX_eq_avgW (ρ : ℝ → ℝ) (u : ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
  (∫ x : ℝ, u x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)) = avgW ρ u δ t := by
  have hδ0 : δ ≠ 0 := hδ.ne'
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℂ, f = fun x => u x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ) := ⟨_, rfl⟩
  have h1 : (∫ w : ℝ, f (t - δ * w)) = |δ⁻¹| • ∫ y : ℝ, f (t - y) :=
    MeasureTheory.Measure.integral_comp_mul_left (fun y => f (t - y)) δ
  rw [integral_sub_left_eq_self f volume t, abs_of_pos (inv_pos.2 hδ), Complex.real_smul] at h1
  have h3 : ∀ w, f (t - δ * w) = ((δ⁻¹ : ℝ) : ℂ) * (u (t - δ * w) * (ρ w : ℂ)) := by
    intro w
    rw [hf]
    have hw : (t - (t - δ * w)) / δ = w := by field_simp; ring
    simp only [hw]
    push_cast
    ring
  have h5 : (∫ w : ℝ, f (t - δ * w)) = ((δ⁻¹ : ℝ) : ℂ) * avgW ρ u δ t := by
    unfold avgW
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall h3)
  rw [h5] at h1
  have hne : ((δ⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (inv_ne_zero hδ0)
  have h6 := mul_left_cancel₀ hne h1
  rw [hf] at h6
  apply h6.symm

private lemma norm_avgW_le (ρ : ℝ → ℝ) (hρi : Integrable ρ) (m : ℕ) (hρm : Integrable (fun w : ℝ => |w| ^ m * ρ w))
  (u : ℝ → ℂ) (B R : ℝ) (hR : 0 ≤ R) (hB : ∀ x, ‖u x‖ ≤ B) (hsupp : ∀ x, R < |x| → u x = 0)
  {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) :
  ‖avgW ρ u δ t‖ ≤ B * ((∫ w, |ρ w|) + ∫ w, |w| ^ m * |ρ w|) * (R + 2) ^ m / (1 + |t|) ^ m := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hC0n : 0 ≤ ∫ w, |ρ w| := integral_nonneg fun w => abs_nonneg _
  have hCmn : 0 ≤ ∫ w, |w| ^ m * |ρ w| :=
    integral_nonneg fun w => mul_nonneg (pow_nonneg (abs_nonneg _) _) (abs_nonneg _)
  have hρa : Integrable (fun w => |ρ w|) := hρi.abs
  have hρma : Integrable (fun w : ℝ => |w| ^ m * |ρ w|) := by
    have h' := hρm.abs
    refine h'.congr (Filter.Eventually.of_forall fun w => ?_)
    show |(|w| ^ m * ρ w)| = |w| ^ m * |ρ w|
    rw [abs_mul, abs_pow, abs_abs]
  have ht1 : 0 < 1 + |t| := by positivity
  have hbasic : ‖avgW ρ u δ t‖ ≤ B * ∫ w, |ρ w| := by
    unfold avgW
    calc
      _ ≤ ∫ w, ‖u (t - δ * w) * (ρ w : ℂ)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ w, B * |ρ w| := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _) (hρa.const_mul B)
          (Filter.Eventually.of_forall fun w => ?_)
        show ‖u (t - δ * w) * (ρ w : ℂ)‖ ≤ B * |ρ w|
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)
      _ = B * ∫ w, |ρ w| := integral_const_mul _ _
  if hcase : |t| ≤ R + 1 then
    have hge : 1 ≤ (R + 2) ^ m / (1 + |t|) ^ m := by
      rw [← div_pow]
      exact one_le_pow₀ ((one_le_div ht1).2 (by linarith))
    calc
      _ ≤ B * ∫ w, |ρ w| := hbasic
      _ = (B * ∫ w, |ρ w|) * 1 := (mul_one _).symm
      _ ≤ (B * ((∫ w, |ρ w|) + ∫ w, |w| ^ m * |ρ w|)) * ((R + 2) ^ m / (1 + |t|) ^ m) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hB0) hge zero_le_one (by positivity)
      _ = B * ((∫ w, |ρ w|) + ∫ w, |w| ^ m * |ρ w|) * (R + 2) ^ m / (1 + |t|) ^ m := by ring
  else
    push Not at hcase
    have hd : 0 < |t| - R := by linarith
    have hpt : ∀ w, ‖u (t - δ * w) * (ρ w : ℂ)‖ ≤ B / (|t| - R) ^ m * (|w| ^ m * |ρ w|) := by
      intro w
      if hw : u (t - δ * w) = 0 then
        rw [hw, zero_mul, norm_zero]
        positivity
      else
        have h1 : |t - δ * w| ≤ R := by
          by_contra h'; exact hw (hsupp _ (not_le.1 h'))
        have h2 : |t| - R ≤ |w| := by
          have h3 : |t| ≤ |t - δ * w| + |δ * w| := by
            refine le_trans ?_ (abs_add_le _ _)
            ·
              apply le_of_eq
              ring_nf
          rw [abs_mul, abs_of_pos hδ] at h3
          have h4 : δ * |w| ≤ |w| := by nlinarith [abs_nonneg w]
          linarith
        have h3 : 1 ≤ (|w| / (|t| - R)) ^ m := one_le_pow₀ ((one_le_div hd).2 h2)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          _ ≤ B * |ρ w| := mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)
          _ = B * 1 * |ρ w| := by rw [mul_one]
          _ ≤ B * (|w| / (|t| - R)) ^ m * |ρ w| :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hB0) (abs_nonneg _)
          _ = B / (|t| - R) ^ m * (|w| ^ m * |ρ w|) := by rw [div_pow]; ring
    have hI : ‖avgW ρ u δ t‖ ≤ B / (|t| - R) ^ m * ∫ w, |w| ^ m * |ρ w| := by
      unfold avgW
      calc
        _ ≤ ∫ w, ‖u (t - δ * w) * (ρ w : ℂ)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ w, B / (|t| - R) ^ m * (|w| ^ m * |ρ w|) :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _) (hρma.const_mul _)
              (Filter.Eventually.of_forall hpt)
        _ = B / (|t| - R) ^ m * ∫ w, |w| ^ m * |ρ w| := integral_const_mul _ _
    have hcmp : (1 + |t|) ^ m ≤ ((R + 2) * (|t| - R)) ^ m :=
      pow_le_pow_left₀ ht1.le (by nlinarith) m
    have hR2 : (0 : ℝ) < (R + 2) ^ m := by positivity
    have hcmp' : 1 / (|t| - R) ^ m ≤ (R + 2) ^ m / (1 + |t|) ^ m := by
      have hre : 1 / (|t| - R) ^ m = (R + 2) ^ m / ((R + 2) * (|t| - R)) ^ m := by
        rw [mul_pow, ← div_div, div_self hR2.ne']
      rw [hre]
      exact div_le_div_of_nonneg_left hR2.le (pow_pos ht1 m) hcmp
    calc
      _ ≤ B / (|t| - R) ^ m * ∫ w, |w| ^ m * |ρ w| := hI
      _ = (B * ∫ w, |w| ^ m * |ρ w|) * (1 / (|t| - R) ^ m) := by ring
      _ ≤ (B * ((∫ w, |ρ w|) + ∫ w, |w| ^ m * |ρ w|)) * ((R + 2) ^ m / (1 + |t|) ^ m) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hB0) hcmp' (by positivity) (by positivity)
      _ = B * ((∫ w, |ρ w|) + ∫ w, |w| ^ m * |ρ w|) * (R + 2) ^ m / (1 + |t|) ^ m := by ring
private lemma tendsto_avgW (ρ : ℝ → ℝ) (hρ : Measurable ρ) (hρi : Integrable ρ) (hρ1 : ∫ w, ρ w = 1)
  (u : ℝ → ℂ) (hu : Measurable u) (B : ℝ) (hB : ∀ x, ‖u x‖ ≤ B) (t : ℝ) (hct : ContinuousAt u t) :
  Filter.Tendsto (fun δ : ℝ => avgW ρ u δ t) (𝓝[>] 0) (𝓝 (u t)) := by
  have hlim : u t = ∫ w, u t * (ρ w : ℂ) := by
    rw [integral_const_mul, integral_complex_ofReal, hρ1]; simp
  rw [hlim]
  unfold avgW
  refine tendsto_integral_filter_of_dominated_convergence (fun w => B * |ρ w|) ?_ ?_ (hρi.abs.const_mul B) ?_
  ·
    refine Filter.Eventually.of_forall fun δ => ?_
    exact ((hu.comp (measurable_const.sub (measurable_const.mul measurable_id))).mul
      (Complex.measurable_ofReal.comp hρ)).aestronglyMeasurable
  ·
    refine Filter.Eventually.of_forall fun δ => Filter.Eventually.of_forall fun w => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)
  ·
    refine Filter.Eventually.of_forall fun w => ?_
    have h1 : Filter.Tendsto (fun δ : ℝ => t - δ * w) (𝓝[>] 0) (𝓝 t) := by
      have : Filter.Tendsto (fun δ : ℝ => t - δ * w) (𝓝 0) (𝓝 (t - 0 * w)) :=
        ((continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0)
      rw [zero_mul, sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine (hct.tendsto.comp h1).mul tendsto_const_nhds

private lemma measurable_avgW (ρ : ℝ → ℝ) (hρ : Measurable ρ) (u : ℝ → ℂ) (hu : Measurable u) (δ : ℝ) :
  Measurable (fun t => avgW ρ u δ t) := by
  have hm : Measurable (fun p : ℝ × ℝ => u (p.1 - δ * p.2) * (ρ p.2 : ℂ)) :=
    (hu.comp (measurable_fst.sub (measurable_const.mul measurable_snd))).mul
      (Complex.measurable_ofReal.comp (hρ.comp measurable_snd))
  refine (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

private lemma one_add_sq_le (t : ℝ) : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
  rw [← sq_abs t]; nlinarith [abs_nonneg t]
/--
[MeasureTheory_memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_memLp_two_and_sum_integral_norm_sq_le_of_forall_norm_sum_integral_conj_scaledKernelAverage_mul_le.lean)
-/
@[path]
private lemma main
  [Fintype ι]
  {Θ : ι → ℝ → ℂ}
  {ρ : ℝ → ℝ}
  {M : ℝ}
-- given
  (hΘ : ∀ i, Continuous (Θ i))
  (hΘg : ∀ i, ∃ (A : ℝ) (k : ℕ), ∀ t, ‖Θ i t‖ ≤ A * (1 + |t|) ^ k)
  (hρ : Measurable ρ)
  (hρm : ∀ n : ℕ, Integrable (fun t : ℝ => |t| ^ n * ρ t))
  (hρ1 : ∫ t : ℝ, ρ t = 1)
  (h : ∀ (u : ι → ℝ → ℂ), (∀ i, Measurable (u i)) → (∃ R : ℝ, ∀ i x, R < |x| → u i x = 0) → (∃ B : ℝ, ∀ i x, ‖u i x‖ ≤ B) → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ‖∑ i, ∫ t : ℝ, conj (∫ x : ℝ, u i x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)) * Θ i t‖ ≤ M * Real.sqrt (∑ i, ∫ t : ℝ, ‖∫ x : ℝ, u i x * ((δ⁻¹ * ρ ((t - x) / δ) : ℝ) : ℂ)‖ ^ 2)) :
-- imply
  (∀ i, MemLp (Θ i) 2) ∧ ∑ i, ∫ t : ℝ, ‖Θ i t‖ ^ 2 ≤ M ^ 2 := by
-- proof
  classical
    have hρi : Integrable ρ := by simpa using hρm 0
    have key : ∀ R : ℝ, 0 ≤ R → ∑ i, ∫ t in Set.Icc (-R) R, ‖Θ i t‖ ^ 2 ≤ M ^ 2 := by
      intro R hR
      have hbd : ∀ i, ∃ C, ∀ x ∈ Set.Icc (-R) R, ‖Θ i x‖ ≤ C := fun i =>
        isCompact_Icc.exists_bound_of_continuousOn (hΘ i).continuousOn
      choose C hC using hbd
      obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = ∑ i, |C i| := ⟨_, rfl⟩
      have hB0 : 0 ≤ B := by rw [hBdef]; exact Finset.sum_nonneg fun j _ => abs_nonneg (C j)
      obtain ⟨u, hu⟩ : ∃ u : ι → ℝ → ℂ, u = fun i => (Set.Icc (-R) R).indicator (Θ i) := ⟨_, rfl⟩
      have hum : ∀ i, Measurable (u i) := fun i => by
        rw [hu]; exact (hΘ i).measurable.indicator measurableSet_Icc
      have hus : ∀ i x, R < |x| → u i x = 0 := by
        intro i x hx
        rw [hu]
        apply Set.indicator_of_notMem
        intro hmem
        rw [Set.mem_Icc, ← abs_le] at hmem
        linarith
      have huB : ∀ i x, ‖u i x‖ ≤ B := by
        intro i x
        rw [hu]
        beta_reduce
        if hx : x ∈ Set.Icc (-R) R then
          rw [Set.indicator_of_mem hx, hBdef]
          calc
            _ ≤ C i := hC i x hx
            _ ≤ |C i| := le_abs_self _
            _ ≤ ∑ j, |C j| := Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)
        else
          rwa [Set.indicator_of_notMem hx, norm_zero]
      have hh : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
          ‖∑ i, ∫ t : ℝ, conj (avgW ρ (u i) δ t) * Θ i t‖ ≤
            M * Real.sqrt (∑ i, ∫ t : ℝ, ‖avgW ρ (u i) δ t‖ ^ 2) := by
        intro δ hδ hδ1
        have h0 := h u hum ⟨R, hus⟩ ⟨B, huB⟩ δ hδ hδ1
        simp only [avgX_eq_avgW ρ _ hδ] at h0
        exact h0
      have hcont : ∀ i t, t ≠ R → t ≠ -R → ContinuousAt (u i) t := by
        intro i t h1 h2
        if ht : |t| < R then
          have hIoo : Set.Ioo (-R) R ∈ 𝓝 t := Ioo_mem_nhds (abs_lt.1 ht).1 (abs_lt.1 ht).2
          have hev : u i =ᶠ[𝓝 t] Θ i := by
            filter_upwards [hIoo] with x hx
            rw [hu]; exact Set.indicator_of_mem (Set.Ioo_subset_Icc_self hx) _
          refine (continuousAt_congr hev).2 (hΘ i).continuousAt
        else
          have hne : |t| ≠ R := fun h' => by
            obtain h'' | h'' := (abs_eq hR).1 h'
            · exact h1 h''
            · exact h2 h''
          have ht' : R < |t| := lt_of_le_of_ne (not_lt.1 ht) (Ne.symm hne)
          have hopen : IsOpen {x : ℝ | R < |x|} := isOpen_lt continuous_const continuous_abs
          have hev : u i =ᶠ[𝓝 t] fun _ => (0 : ℂ) := by
            filter_upwards [hopen.mem_nhds ht'] with x hx
            exact hus i x hx
          refine (continuousAt_congr hev).2 continuousAt_const
      have hae : ∀ᵐ t : ℝ, t ≠ R ∧ t ≠ -R := by
        have h0 : volume ({R, -R} : Set ℝ) = 0 := (Set.toFinite {R, -R}).measure_zero volume
        filter_upwards [compl_mem_ae_iff.2 h0] with t ht
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht
        exact ht
      have hC0n : 0 ≤ ∫ w, |ρ w| := integral_nonneg fun w => abs_nonneg _
      have hCmn : ∀ m : ℕ, 0 ≤ ∫ w : ℝ, |w| ^ m * |ρ w| := fun m =>
        integral_nonneg fun w => mul_nonneg (pow_nonneg (abs_nonneg _) _) (abs_nonneg _)
      have L1 : ∀ i, Filter.Tendsto (fun δ : ℝ => ∫ t : ℝ, conj (avgW ρ (u i) δ t) * Θ i t) (𝓝[>] 0)
        (𝓝 (∫ t : ℝ, conj (u i t) * Θ i t)) := by
        intro i
        obtain ⟨A, k, hAk⟩ := hΘg i
        have hA0 : 0 ≤ A := by
          have h0 := (norm_nonneg _).trans (hAk 0)
          simpa using h0
        obtain ⟨P, hP⟩ : ∃ P : ℝ, P = B * ((∫ w, |ρ w|) + ∫ w : ℝ, |w| ^ (k + 2) * |ρ w|) * (R + 2) ^ (k + 2) := ⟨_, rfl⟩
        have hP0 : 0 ≤ P := by rw [hP]; exact mul_nonneg (mul_nonneg hB0 (add_nonneg hC0n (hCmn _))) (by positivity)
        refine tendsto_integral_filter_of_dominated_convergence (fun t => P * A * (1 + t ^ 2)⁻¹) ?_ ?_
          (integrable_inv_one_add_sq.const_mul (P * A)) ?_
        ·
          refine Filter.Eventually.of_forall fun δ => ?_
          exact ((Complex.continuous_conj.measurable.comp (measurable_avgW ρ hρ (u i) (hum i) δ)).mul
            (hΘ i).measurable).aestronglyMeasurable
        ·
          filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ
          refine Filter.Eventually.of_forall fun t => ?_
          have hav := norm_avgW_le ρ hρi (k + 2) (hρm (k + 2)) (u i) B R hR (huB i) (hus i) hδ.1 hδ.2 t
          rw [← hP] at hav
          have ht1 : (0 : ℝ) < 1 + |t| := by positivity
          rw [norm_mul, RCLike.norm_conj]
          calc
            _ ≤ (P / (1 + |t|) ^ (k + 2)) * (A * (1 + |t|) ^ k) :=
                mul_le_mul hav (hAk t) (norm_nonneg _) (by positivity)
            _ = P * A * ((1 + |t|) ^ 2)⁻¹ := by
              rw [pow_add]
              field_simp
            _ ≤ P * A * (1 + t ^ 2)⁻¹ :=
                mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (one_add_sq_le t)) (by positivity)
        ·
          filter_upwards [hae] with t ht
          exact ((Complex.continuous_conj.tendsto _).comp
            (tendsto_avgW ρ hρ hρi hρ1 (u i) (hum i) B (huB i) t (hcont i t ht.1 ht.2))).mul
            tendsto_const_nhds
      have L2 : ∀ i, Filter.Tendsto (fun δ : ℝ => ∫ t : ℝ, ‖avgW ρ (u i) δ t‖ ^ 2) (𝓝[>] 0)
        (𝓝 (∫ t : ℝ, ‖u i t‖ ^ 2)) := by
        intro i
        obtain ⟨P, hP⟩ : ∃ P : ℝ, P = B * ((∫ w, |ρ w|) + ∫ w : ℝ, |w| ^ 1 * |ρ w|) * (R + 2) ^ 1 := ⟨_, rfl⟩
        have hP0 : 0 ≤ P := by rw [hP]; exact mul_nonneg (mul_nonneg hB0 (add_nonneg hC0n (hCmn _))) (by positivity)
        refine tendsto_integral_filter_of_dominated_convergence (fun t => P ^ 2 * (1 + t ^ 2)⁻¹) ?_ ?_
          (integrable_inv_one_add_sq.const_mul (P ^ 2)) ?_
        ·
          refine Filter.Eventually.of_forall fun δ => ?_
          exact ((measurable_avgW ρ hρ (u i) (hum i) δ).norm.pow_const 2).aestronglyMeasurable
        ·
          filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ
          refine Filter.Eventually.of_forall fun t => ?_
          have hav := norm_avgW_le ρ hρi 1 (hρm 1) (u i) B R hR (huB i) (hus i) hδ.1 hδ.2 t
          rw [← hP, pow_one] at hav
          have ht1 : (0 : ℝ) < 1 + |t| := by positivity
          rw [Real.norm_eq_abs, abs_pow, abs_norm]
          calc
            _ ≤ (P / (1 + |t|)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hav 2
            _ = P ^ 2 * ((1 + |t|) ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
            _ ≤ P ^ 2 * (1 + t ^ 2)⁻¹ :=
                mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (one_add_sq_le t)) (sq_nonneg _)
        ·
          filter_upwards [hae] with t ht
          exact ((tendsto_avgW ρ hρ hρi hρ1 (u i) (hum i) B (huB i) t (hcont i t ht.1 ht.2)).norm).pow 2
      have LHSlim : Filter.Tendsto (fun δ : ℝ => ‖∑ i, ∫ t : ℝ, conj (avgW ρ (u i) δ t) * Θ i t‖) (𝓝[>] 0)
        (𝓝 ‖∑ i, ∫ t : ℝ, conj (u i t) * Θ i t‖) := (tendsto_finsetSum _ fun i _ => L1 i).norm
      have RHSlim : Filter.Tendsto (fun δ : ℝ => M * Real.sqrt (∑ i, ∫ t : ℝ, ‖avgW ρ (u i) δ t‖ ^ 2)) (𝓝[>] 0)
        (𝓝 (M * Real.sqrt (∑ i, ∫ t : ℝ, ‖u i t‖ ^ 2))) :=
        ((tendsto_finsetSum _ fun i _ => L2 i).sqrt).const_mul M
      have hnear := by
        filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ
        exact hh δ hδ.1 hδ.2
      have hle : ‖∑ i, ∫ t : ℝ, conj (u i t) * Θ i t‖ ≤ M * Real.sqrt (∑ i, ∫ t : ℝ, ‖u i t‖ ^ 2) :=
        le_of_tendsto_of_tendsto LHSlim RHSlim hnear
      have hX1 : ∀ i, (∫ t : ℝ, conj (u i t) * Θ i t) = ((∫ t in Set.Icc (-R) R, ‖Θ i t‖ ^ 2 : ℝ) : ℂ) := by
        intro i
        rw [← integral_indicator measurableSet_Icc, ← integral_complex_ofReal]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        rw [hu]
        simp only [Set.indicator_apply]
        split_ifs with ht
        ·
          rw [Complex.conj_mul']; push_cast; ring
        · simp
      have hX2 : ∀ i, (∫ t : ℝ, ‖u i t‖ ^ 2) = ∫ t in Set.Icc (-R) R, ‖Θ i t‖ ^ 2 := by
        intro i
        rw [← integral_indicator measurableSet_Icc]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        rw [hu]
        simp only [Set.indicator_apply]
        split_ifs <;> simp
      obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ i, ∫ t in Set.Icc (-R) R, ‖Θ i t‖ ^ 2 := ⟨_, rfl⟩
      have hX0 : 0 ≤ X := by rw [hX]; exact Finset.sum_nonneg fun i _ => integral_nonneg fun t => by positivity
      simp only [hX1, hX2] at hle
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg (hX ▸ hX0), ← hX] at hle
      rw [← hX]
      if hX00 : X = 0 then
        rw [hX00]
        positivity
      else
        have hXpos : 0 < X := lt_of_le_of_ne hX0 (Ne.symm hX00)
        have h1 : Real.sqrt X * Real.sqrt X ≤ M * Real.sqrt X := by rwa [Real.mul_self_sqrt hX0]
        have hs : Real.sqrt X ≤ M := le_of_mul_le_mul_right h1 (Real.sqrt_pos.2 hXpos)
        calc
          _ = Real.sqrt X ^ 2 := (Real.sq_sqrt hX0).symm
          _ ≤ M ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg X) hs 2
    have hf_int : ∀ i (a b : ℝ), IntegrableOn (fun t => ‖Θ i t‖ ^ 2) (Set.Icc a b) := fun i a b =>
      (((hΘ i).norm.pow 2).continuousOn).integrableOn_compact isCompact_Icc
    have hcover : AECover volume Filter.atTop (fun n : ℕ => Set.Icc (-(n : ℝ)) (n : ℝ)) :=
      aecover_Icc (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
    have hsingle : ∀ i (n : ℕ), ∫ t in Set.Icc (-(n : ℝ)) n, ‖Θ i t‖ ^ 2 ≤ M ^ 2 := by
      intro i n
      refine le_trans ?_ (key n (Nat.cast_nonneg n))
      exact Finset.single_le_sum (f := fun j => ∫ t in Set.Icc (-(n : ℝ)) n, ‖Θ j t‖ ^ 2)
        (fun j _ => integral_nonneg fun t => by positivity) (Finset.mem_univ i)
    have hInt : ∀ i, Integrable (fun t => ‖Θ i t‖ ^ 2) := by
      intro i
      refine hcover.integrable_of_integral_norm_bounded (M ^ 2) (fun n => hf_int i _ _) ?_
      refine Filter.Eventually.of_forall fun n => le_trans (le_of_eq ?_) (hsingle i n)
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [Real.norm_eq_abs, abs_pow, abs_norm]
    refine ⟨fun i => (memLp_two_iff_integrable_sq_norm (hΘ i).aestronglyMeasurable).2 (hInt i), ?_⟩
    have hlim : Filter.Tendsto (fun n : ℕ => ∑ i, ∫ t in Set.Icc (-(n : ℝ)) n, ‖Θ i t‖ ^ 2) Filter.atTop
      (𝓝 (∑ i, ∫ t, ‖Θ i t‖ ^ 2)) :=
      tendsto_finsetSum _ fun i _ => hcover.integral_tendsto_of_countably_generated (hInt i)
    refine le_of_tendsto' hlim fun n => key n (Nat.cast_nonneg n)


-- created on 2026-10-23
