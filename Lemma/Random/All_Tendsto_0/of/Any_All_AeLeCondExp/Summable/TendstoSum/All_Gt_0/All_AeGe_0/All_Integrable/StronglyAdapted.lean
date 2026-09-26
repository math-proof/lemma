import Mathlib.Probability.Martingale.Convergence
import Lemma.Random.All_Summable.of.Summable_Integral.All_AeGe_0.All_Integrable
import Lemma.Random.Any_All_LeELpNorm.of.Any_All_LeIntegral.Submartingale
import Lemma.Random.AddSub.aeLe.CondExpSub.of.All_AeLeCondExp.Summable.All_Integrable
import Lemma.Real.Eq_0.of.Tendsto.Summable_Mul.All_Ge_0.TendstoSum.All_Gt_0
open MeasureTheory Filter Finset Topology Random Real


@[main]
private lemma main
  [m₀ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀}
  {f : ℕ → Ω → ℝ}
  {T : ℕ → ℝ}
-- given
  (h₀ : StronglyAdapted ℱ f)
  (h₁ : ∀ n, Integrable (f n) μ)
  (h₂ : ∀ n, 0 ≤ᵐ[μ] f n)
  (h₃ : ∀ n, 0 < T n)
  (h₄ : Tendsto (fun n => ∑ k ∈ range n, T k) atTop atTop)
  (h₅ : Summable fun n => T n ^ 2)
  (h₆ : ∃ C ≥ 0, ∀ n, μ[f (n + 1) | ℱ n] ≤ᵐ[μ] fun ω => (1 - T n) * f n ω + C * T n ^ 2) :
-- imply
  ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
-- proof
  obtain ⟨C, hC, h₆⟩ := h₆
  let W : ℕ → Ω → ℝ := fun n ω => -f n ω - C * ∑' k, T (k + n) ^ 2
  have hstep : ∀ n, (fun ω => W n ω + T n * f n ω) ≤ᵐ[μ] μ[W (n + 1) | ℱ n] :=
    AddSub.aeLe.CondExpSub.of.All_AeLeCondExp.Summable.All_Integrable h₁ h₅ h₆
  have hint : ∀ n, Integrable (W n) μ := fun n => (h₁ n).neg.sub (integrable_const _)
  have hnonpos : ∀ n, W n ≤ᵐ[μ] 0 := fun n => (h₂ n).mono fun ω hω => by
    have : 0 ≤ C * ∑' k, T (k + n) ^ 2 := mul_nonneg hC (tsum_nonneg fun k => sq_nonneg _)
    simp only [Pi.zero_apply, W] at hω ⊢
    linarith
  have hsub : Submartingale W ℱ μ := by
    refine submartingale_nat (fun n => (h₀ n).neg.sub stronglyMeasurable_const) hint fun n => ?_
    filter_upwards [hstep n, h₂ n] with ω h₇ h₈
    have := mul_nonneg (h₃ n).le h₈
    linarith
  obtain ⟨R, hR⟩ := Any_All_LeELpNorm.of.Any_All_LeIntegral.Submartingale hsub
    ⟨0, fun n => integral_nonpos_of_ae ((hnonpos n).mono fun ω hω => posPart_nonpos.2 hω)⟩
  have htail : Tendsto (fun n => C * ∑' k, T (k + n) ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_sum_nat_add fun k => T k ^ 2).const_mul C
  have hconv : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
    filter_upwards [hsub.exists_ae_tendsto_of_bdd hR] with ω ⟨c, hc⟩
    have := (hc.add htail).neg
    rw [add_zero] at this
    exact ⟨-c, this.congr fun n => by simp [W]⟩
  have hsum : Summable fun n => ∫ ω, T n * f n ω ∂μ := by
    refine summable_of_sum_range_le (c := -∫ ω, W 0 ω ∂μ) (fun n => integral_nonneg_of_ae ((h₂ n).mono fun ω hω => mul_nonneg (h₃ n).le hω)) fun n => ?_
    have hle : ∀ i, ∫ ω, T i * f i ω ∂μ ≤ ∫ ω, W (i + 1) ω ∂μ - ∫ ω, W i ω ∂μ := fun i => by
      have := integral_mono_ae ((hint i).add ((h₁ i).const_mul (T i))) integrable_condExp (hstep i)
      rw [integral_condExp (ℱ.le i), integral_add' (hint i) ((h₁ i).const_mul (T i))] at this
      linarith
    calc
      _ ≤ ∑ i ∈ range n, (∫ ω, W (i + 1) ω ∂μ - ∫ ω, W i ω ∂μ) := sum_le_sum fun i _ => hle i
      _ = ∫ ω, W n ω ∂μ - ∫ ω, W 0 ω ∂μ := sum_range_sub (fun i => ∫ ω, W i ω ∂μ) n
      _ ≤ _ := by linarith [integral_nonpos_of_ae (hnonpos n)]
  filter_upwards [All_Summable.of.Summable_Integral.All_AeGe_0.All_Integrable (fun n => (h₁ n).const_mul (T n)) (fun n => (h₂ n).mono fun ω hω => mul_nonneg (h₃ n).le hω) hsum, hconv, ae_all_iff.2 h₂] with ω hs ⟨c, hc⟩ hnn
  rwa [Eq_0.of.Tendsto.Summable_Mul.All_Ge_0.TendstoSum.All_Gt_0 h₃ h₄ hnn hs hc] at hc


-- created on 2026-09-26