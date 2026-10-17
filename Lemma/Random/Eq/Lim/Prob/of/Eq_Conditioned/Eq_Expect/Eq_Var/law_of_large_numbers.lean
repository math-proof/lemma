import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecificLimits.Basic
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset Filter


/--
Weak law of large numbers: for pairwise independent random variables with common mean `μ`
and common variance `σ²`, the sample average converges to `μ` in probability.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → ℝ}
  {μ σ ε : ℝ}
-- given
  (h₀ : ∀ i j, i ≠ j → IndepFun (x i) (x j) π)
  (h₁ : ∀ i, MemLp (x i) 2 π)
  (hmeas : ∀ i, Measurable (x i))
  (h₂ : ∀ i, π[x i] = μ)
  (h₃ : ∀ i, variance (x i) π = σ ^ 2)
  (h₄ : 0 < ε) :
-- imply
  Tendsto (fun n : ℕ =>
      π.real {ω | |(∑ i ∈ range (n + 1), x i ω) / ((n : ℝ) + 1) - μ| < ε})
    atTop (nhds 1) := by
-- proof
  let avg : ℕ → Ω → ℝ := fun n ω => ((n : ℝ) + 1)⁻¹ * ∑ i ∈ range (n + 1), x i ω
  have hmeas_avg : ∀ n, Measurable (avg n) := fun n =>
    ((Finset.measurable_sum (range (n + 1)) fun i _ => hmeas i).const_mul _)
  have hmem : ∀ n, MemLp (avg n) 2 π := fun n => by
    simpa [avg, Finset.sum_apply] using
      (memLp_finsetSum' (range (n + 1)) fun i _ => h₁ i).const_mul ((n : ℝ) + 1)⁻¹
  have hmean : ∀ n, π[avg n] = μ := by
    intro n
    rw [integral_const_mul, integral_finsetSum _ fun i _ => (h₁ i).integrable one_le_two,
      Finset.sum_congr rfl fun i _ => h₂ i, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_succ]
    field_simp
  have hvar : ∀ n, variance (avg n) π = σ ^ 2 / ((n : ℝ) + 1) := by
    intro n
    rw [variance_const_mul,
      show (fun ω => ∑ i ∈ range (n + 1), x i ω) = ∑ i ∈ range (n + 1), x i from
        funext fun ω => (Finset.sum_apply ω (range (n + 1)) x).symm,
      IndepFun.variance_sum (fun i _ => h₁ i) (fun i _ j _ hij => h₀ i j hij),
      Finset.sum_congr rfl fun i _ => h₃ i, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_succ]
    field_simp
  have htail : Tendsto (fun n => π.real {ω | ε ≤ |avg n ω - μ|}) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ℝ))
      (h := fun n => (σ ^ 2 * (ε ^ 2)⁻¹) * ((n : ℝ) + 1)⁻¹)
      tendsto_const_nhds ?_ (fun _ => measureReal_nonneg) ?_
    · simpa [mul_zero] using ((tendsto_const_nhds (x := σ ^ 2 * (ε ^ 2)⁻¹)).mul ((tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).inv_tendsto_atTop))
    ·
      intro n
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      simpa [measureReal_def, hmean n, hvar n, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        meas_ge_le_variance_div_sq (μ := π) (hmem n) h₄
  have hcompl : ∀ n, π.real {ω | |avg n ω - μ| < ε} = 1 - π.real {ω | ε ≤ |avg n ω - μ|} := by
    intro n
    have hs : MeasurableSet {ω | ε ≤ |avg n ω - μ|} :=
      measurableSet_le measurable_const
        (continuous_abs.measurable.comp ((hmeas_avg n).sub measurable_const))
    have hset : {ω | |avg n ω - μ| < ε} = {ω | ε ≤ |avg n ω - μ|}ᶜ := by
      ext ω
      simp
    rw [hset, measureReal_compl hs]
    simp [measure_univ, measureReal_def]
  have hdiv : ∀ n, {ω | |(∑ i ∈ range (n + 1), x i ω) / ((n : ℝ) + 1) - μ| < ε} =
      {ω | |avg n ω - μ| < ε} := by
    intro n
    ext ω
    simp [avg, div_eq_mul_inv, mul_comm]
  simpa [hdiv, hcompl] using (tendsto_const_nhds.sub htail)


-- created on 2023-04-18
-- updated on 2026-10-17
