import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal ENNReal


namespace ChernoffBound

/--
[chernoff_bound_bounded_rv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ChernoffBound.lean)
-/
@[path]
lemma chernoff_bound_bounded_rv
  {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω}
  {n : ℕ}
  {X : ℕ → Ω → ℝ}
  {t : ℝ}
-- given
  (hn : 0 < n)
  (h_indep : iIndepFun X μ)
  (h_meas : ∀ i, AEMeasurable (X i) μ)
  (h_bounded : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1)
  (h_mean : ∀ i, μ[X i] = 0)
  (ht : 0 < t) :
-- imply
  μ.real {ω | t * Real.sqrt n ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-t ^ 2 / 2) := by
-- proof
  have hprob : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have h_subG : ∀ i < n, HasSubgaussianMGF (X i) 1 μ := by
    intro i _
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (h_meas i) (h_bounded i) (h_mean i)
    convert h using 1
    show (1 : NNReal) = (‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2
    simp only [show (1 : ℝ) - (-1) = (2 : ℝ) from by ring, Real.nnnorm_two]
    norm_num
  have hε : (0 : ℝ) ≤ t * Real.sqrt n := by positivity
  have hn_cast : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  calc μ.real {ω | t * Real.sqrt n ≤ ∑ i ∈ Finset.range n, X i ω}
    ≤ Real.exp (-(t * Real.sqrt n) ^ 2 / (2 * ↑n * ↑(1 : NNReal))) :=
      HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun h_indep h_subG hε
    _ = Real.exp (-t ^ 2 / 2) := by
      congr 1
      simp only [NNReal.coe_one, mul_one, mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg' n)]
      field_simp
set_option maxHeartbeats 400000 in

end ChernoffBound

namespace ChernoffBound

/--
[chernoff_bernoulli_upper_tail](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ChernoffBound.lean)
-/
@[path]
lemma chernoff_bernoulli_upper_tail
  {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω}
  {n : ℕ}
  {X : ℕ → Ω → ℝ}
  {t : ℝ}
-- given
  (hn : 0 < n)
  (h_indep : iIndepFun X μ)
  (h_meas : ∀ i, AEMeasurable (X i) μ)
  (h_bernoulli : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ ({0, 1} : Set ℝ))
  (ht : 0 < t) :
-- imply
  μ.real {ω | (∑ i ∈ Finset.range n, μ[X i]) + t * Real.sqrt n ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-t ^ 2 / 2) := by
-- proof
  have hprob : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have h_event_eq : {ω | (∑ i ∈ Finset.range n, μ[X i]) + t * Real.sqrt n ≤
    ∑ i ∈ Finset.range n, X i ω} =
    {ω | t * Real.sqrt n ≤ ∑ i ∈ Finset.range n, (X i ω - μ[X i])} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith [Finset.sum_sub_distrib
      (f := fun i => X i ω) (g := fun i => (μ[X i] : ℝ)) (s := Finset.range n)]
  rw [h_event_eq]
  have h_indep_Y : iIndepFun (fun i ω => X i ω - μ[X i]) μ := by
    have : (fun i ω => X i ω - (μ[X i] : ℝ)) = (fun i => (fun x => x - μ[X i]) ∘ X i) := by
      ext i ω; simp [Function.comp]
    rw [this]
    exact h_indep.comp _ (fun _ => measurable_sub_const _)
  have h_subG : ∀ i < n, HasSubgaussianMGF (fun ω => X i ω - μ[X i]) (1 : NNReal) μ := by
    intro i _
    have h_int : Integrable (X i) μ :=
      (integrable_const (1 : ℝ)).mono' (h_meas i).aestronglyMeasurable (by
        filter_upwards [h_bernoulli i] with ω hω
        cases hω with
        | inl h0 => simp [h0]
        | inr h1 => simp [Set.mem_singleton_iff.mp h1])
    have h_nn : (0 : ℝ) ≤ μ[X i] := by
      apply integral_nonneg_of_ae
      filter_upwards [h_bernoulli i] with ω hω
      show (0 : Ω → ℝ) ω ≤ X i ω
      simp only [Pi.zero_apply]
      cases hω with
      | inl h0 => linarith
      | inr h1 => linarith [Set.mem_singleton_iff.mp h1]
    have h_le1 : μ[X i] ≤ 1 := by
      have h_le : ∀ᵐ ω ∂μ, X i ω ≤ (fun _ => (1 : ℝ)) ω := by
        filter_upwards [h_bernoulli i] with ω hω
        cases hω with
        | inl h0 => simp [h0]
        | inr h1 => simp [Set.mem_singleton_iff.mp h1]
      have := integral_mono_ae h_int (integrable_const _) h_le
      simp [integral_const] at this
      exact this
    have h_bounded : ∀ᵐ ω ∂μ, (X i ω - μ[X i]) ∈ Set.Icc (-1 : ℝ) 1 := by
      filter_upwards [h_bernoulli i] with ω hω
      cases hω with
      | inl h0 => exact ⟨by linarith, by linarith⟩
      | inr h1 =>
        have h1' := Set.mem_singleton_iff.mp h1
        exact ⟨by linarith, by linarith⟩
    have h_mean : μ[fun ω => X i ω - μ[X i]] = 0 := by
      simp [integral_sub h_int (integrable_const _)]
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      ((h_meas i).sub aemeasurable_const) h_bounded h_mean
    convert h using 1
    show (1 : NNReal) = (‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2
    simp only [show (1 : ℝ) - (-1) = (2 : ℝ) from by ring, Real.nnnorm_two]
    norm_num
  have hε : (0 : ℝ) ≤ t * Real.sqrt n := by positivity
  calc μ.real {ω | t * Real.sqrt n ≤ ∑ i ∈ Finset.range n, (X i ω - μ[X i])}
    ≤ Real.exp (-(t * Real.sqrt n) ^ 2 / (2 * ↑n * (1 : ℝ))) :=
      HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun h_indep_Y h_subG hε
    _ = Real.exp (-t ^ 2 / 2) := by
      congr 1
      simp only [mul_one, mul_pow, Real.sq_sqrt (Nat.cast_nonneg' n)]
      field_simp
set_option maxHeartbeats 400000 in

end ChernoffBound

namespace ChernoffBound

/--
[chernoff_bernoulli_lower_tail](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ChernoffBound.lean)
-/
@[path]
lemma chernoff_bernoulli_lower_tail
  {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω}
  {n : ℕ}
  {X : ℕ → Ω → ℝ}
  {t : ℝ}
-- given
  (hn : 0 < n)
  (h_indep : iIndepFun X μ)
  (h_meas : ∀ i, AEMeasurable (X i) μ)
  (h_bernoulli : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ ({0, 1} : Set ℝ))
  (ht : 0 < t) :
-- imply
  μ.real {ω | ∑ i ∈ Finset.range n, X i ω ≤ (∑ i ∈ Finset.range n, μ[X i]) - t * Real.sqrt n} ≤ Real.exp (-t ^ 2 / 2) := by
-- proof
  have hprob : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  have h_event_eq : {ω | ∑ i ∈ Finset.range n, X i ω ≤
    (∑ i ∈ Finset.range n, μ[X i]) - t * Real.sqrt n} =
    {ω | t * Real.sqrt n ≤ ∑ i ∈ Finset.range n, (μ[X i] - X i ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith [Finset.sum_sub_distrib
      (f := fun i => (μ[X i] : ℝ)) (g := fun i => X i ω) (s := Finset.range n)]
  rw [h_event_eq]
  have h_indep_Z : iIndepFun (fun i ω => μ[X i] - X i ω) μ := by
    have : (fun i ω => μ[X i] - X i ω) = (fun i => (fun x => μ[X i] - x) ∘ X i) := by
      ext i ω; simp [Function.comp]
    rw [this]
    exact h_indep.comp _ (fun _ => measurable_const.sub measurable_id)
  have h_subG : ∀ i < n, HasSubgaussianMGF (fun ω => μ[X i] - X i ω) (1 : NNReal) μ := by
    intro i _
    have h_int : Integrable (X i) μ :=
      (integrable_const (1 : ℝ)).mono' (h_meas i).aestronglyMeasurable (by
        filter_upwards [h_bernoulli i] with ω hω
        cases hω with
        | inl h0 => simp [h0]
        | inr h1 => simp [Set.mem_singleton_iff.mp h1])
    have h_nn : (0 : ℝ) ≤ μ[X i] := by
      apply integral_nonneg_of_ae
      filter_upwards [h_bernoulli i] with ω hω
      show (0 : Ω → ℝ) ω ≤ X i ω
      simp only [Pi.zero_apply]
      cases hω with
      | inl h0 => linarith
      | inr h1 => linarith [Set.mem_singleton_iff.mp h1]
    have h_le1 : μ[X i] ≤ 1 := by
      have h_le : ∀ᵐ ω ∂μ, X i ω ≤ (fun _ => (1 : ℝ)) ω := by
        filter_upwards [h_bernoulli i] with ω hω
        cases hω with
        | inl h0 => simp [h0]
        | inr h1 => simp [Set.mem_singleton_iff.mp h1]
      have := integral_mono_ae h_int (integrable_const _) h_le
      simp [integral_const] at this
      exact this
    have h_bounded : ∀ᵐ ω ∂μ, (μ[X i] - X i ω) ∈ Set.Icc (-1 : ℝ) 1 := by
      filter_upwards [h_bernoulli i] with ω hω
      cases hω with
      | inl h0 => exact ⟨by linarith, by linarith⟩
      | inr h1 =>
        have h1' := Set.mem_singleton_iff.mp h1
        exact ⟨by linarith, by linarith⟩
    have h_mean : μ[fun ω => μ[X i] - X i ω] = 0 := by
      simp [integral_sub (integrable_const _) h_int]
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (aemeasurable_const.sub (h_meas i)) h_bounded h_mean
    convert h using 1
    show (1 : NNReal) = (‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2
    simp only [show (1 : ℝ) - (-1) = (2 : ℝ) from by ring, Real.nnnorm_two]
    norm_num
  have hε : (0 : ℝ) ≤ t * Real.sqrt n := by positivity
  calc μ.real {ω | t * Real.sqrt n ≤ ∑ i ∈ Finset.range n, (μ[X i] - X i ω)}
    ≤ Real.exp (-(t * Real.sqrt n) ^ 2 / (2 * ↑n * (1 : ℝ))) :=
      HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun h_indep_Z h_subG hε
    _ = Real.exp (-t ^ 2 / 2) := by
      congr 1
      simp only [mul_one, mul_pow, Real.sq_sqrt (Nat.cast_nonneg' n)]
      field_simp

end ChernoffBound

namespace ChernoffBound

/--
[chernoff_bernoulli_tail](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ChernoffBound.lean)
-/
@[path]
lemma chernoff_bernoulli_tail
  {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω}
  {n : ℕ}
  {X : ℕ → Ω → ℝ}
  {t : ℝ}
-- given
  (hn : 0 < n)
  (h_indep : iIndepFun X μ)
  (h_meas : ∀ i, AEMeasurable (X i) μ)
  (h_bernoulli : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ ({0, 1} : Set ℝ))
  (ht : 0 < t) :
-- imply
  μ.real {ω | (∑ i ∈ Finset.range n, μ[X i]) + t * Real.sqrt n ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-t ^ 2 / 2) ∧ μ.real {ω | ∑ i ∈ Finset.range n, X i ω ≤ (∑ i ∈ Finset.range n, μ[X i]) - t * Real.sqrt n} ≤ Real.exp (-t ^ 2 / 2) :=
-- proof
  ⟨chernoff_bernoulli_upper_tail hn h_indep h_meas h_bernoulli ht,
    chernoff_bernoulli_lower_tail hn h_indep h_meas h_bernoulli ht⟩

end ChernoffBound


-- created on 2026-10-23
