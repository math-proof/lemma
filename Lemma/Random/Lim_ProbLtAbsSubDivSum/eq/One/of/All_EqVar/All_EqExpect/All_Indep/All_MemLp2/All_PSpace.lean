import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecificLimits.Basic
import Notation.Fun
import Notation.Algebra.Power
import Notation.Analysis.Real.Numbers
import Def.Analysis.Real.Limits.Basic
import Lemma.Random.Var.eq.Integral
import Lemma.Random.Expect.eq.Integral
import Lemma.Random.All_Indep.of.All_Indep_GetSlice
import Theorem.Probability.JointRv.AsRV
open MeasureTheory ProbabilityTheory Finset Filter Fun Random


/--
Weak law of large numbers: for random variables independent of their past, with common mean `μ`
and common variance `σ²`, the sample average converges to `μ` in probability.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ ⇀ Ω → ℝ}
  {μ σ : ℝ} {ε : ℝ⁺}
-- given
  (h₀ : ∀ k, PSpace π x[k])
  (h₁ : ∀ k, MemLp x[k] 2 π)
  (h₂ : ∀ k, x[k] ⟂ᵢ[π] x[:k])
  (h₃ : ∀ k, 𝔼[x[k]: π](x[k]) = μ)
  (h₄ : ∀ k, 𝕍𝕒𝕣[x[k]: π](x[k]) = σ²) :
-- imply
  lim[n → ∞] ℙ[π]{|(∑ i ∈ range n, x[i]) / (n : ℝ) - μ| < ε} = 1 := by
-- proof
  have hvar₀ : ∀ i, variance x[i] π = σ² := fun i => by
    have := h₀ i
    rw [variance_eq_integral (PSpace.aemeasurable (x := x[i])), ← Var.eq.Integral]
    apply h₄ i
  have h₃' : ∀ i, π[x[i]] = μ := fun i => by
    have := h₀ i
    simpa [← Expect.eq.Integral, Expectation.asRV_function] using h₃ i
  have hpair : ∀ i j (_ : i ≠ j), x[i] ⟂ᵢ[π] x[j] := All_Indep.of.All_Indep_GetSlice h₂
  let avg : ℕ → Ω → ℝ := fun n ω => (n : ℝ)⁻¹ * ∑ i ∈ range n, x[i] ω
  have hmem : ∀ n, MemLp (avg n) 2 π := fun n => by
    simpa [avg, Finset.sum_apply] using
      (memLp_finsetSum' (range n) fun i _ => h₁ i).const_mul (n : ℝ)⁻¹
  have hmean : ∀ n ≠ 0, π[avg n] = μ := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [integral_const_mul, integral_finsetSum _ fun i _ => (h₁ i).integrable one_le_two,
      Finset.sum_congr rfl fun i _ => h₃' i, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hn0]
  have hvar : ∀ n ≠ 0, variance (avg n) π = σ² / (n : ℝ) := by
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [variance_const_mul,
      show (fun ω => ∑ i ∈ range n, x[i] ω) = ∑ i ∈ range n, x[i] from
        funext fun ω => (Finset.sum_apply ω (range n) (fun i => x[i])).symm,
      IndepFun.variance_sum (fun i _ => h₁ i) (fun i _ j _ hij => hpair i j hij),
      Finset.sum_congr rfl fun i _ => hvar₀ i, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp [hn0]
  have htail : Tendsto (fun n => π.real {ω | ε ≤ |avg n ω - μ|}) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun _ : ℕ => (0 : ℝ))
      (h := fun n => (σ² * ((ε : ℝ)²)⁻¹) * (n : ℝ)⁻¹)
      tendsto_const_nhds ?_ ?_ ?_
    ·
      simpa [mul_zero] using
        (tendsto_const_nhds (x := σ² * ((ε : ℝ)²)⁻¹)).mul tendsto_inv_atTop_nhds_zero_nat
    · exact Eventually.of_forall fun _ => measureReal_nonneg
    ·
      filter_upwards [eventually_ne_atTop 0] with n hn
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      simpa [measureReal_def, hmean n hn, hvar n hn, div_eq_mul_inv, mul_assoc, mul_left_comm,
        mul_comm] using meas_ge_le_variance_div_sq (μ := π) (hmem n) ε.property
  have hcompl : ∀ n, π.real {ω | |avg n ω - μ| < ε} = 1 - π.real {ω | ε ≤ |avg n ω - μ|} := by
    intro n
    have hs : NullMeasurableSet {ω | ε ≤ |avg n ω - μ|} π :=
      AEStronglyMeasurable.nullMeasurableSet_le aestronglyMeasurable_const
        (((hmem n).aestronglyMeasurable.sub aestronglyMeasurable_const).norm)
    have hset : {ω | |avg n ω - μ| < ε} = {ω | ε ≤ |avg n ω - μ|}ᶜ := by
      ext ω
      simp
    rw [hset, measureReal_compl₀ hs]
    simp [measureReal_def, measure_univ]
  have hdiv : ∀ n, {ω | |(∑ i ∈ range n, x[i] ω) / (n : ℝ) - μ| < ε} =
      {ω | |avg n ω - μ| < ε} := by
    intro n
    ext ω
    simp [avg, div_eq_mul_inv, mul_comm]
  simpa [hdiv, hcompl] using (tendsto_const_nhds.sub htail)


-- created on 2023-04-18
-- updated on 2026-11-12
