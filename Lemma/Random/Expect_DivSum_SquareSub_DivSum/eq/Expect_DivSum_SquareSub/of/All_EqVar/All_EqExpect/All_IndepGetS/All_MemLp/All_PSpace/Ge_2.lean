import Mathlib.Probability.Moments.Variance
import Notation.Fun
import Notation.Algebra.Power
import Instance.Data.Nat.Fun
import Instance.Probability.Process.HiddenMarkovSequence
import Lemma.Random.Var.eq.Integral
import Lemma.Random.Expect.eq.Integral
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import Theorem.Probability.JointRv.AsRV
open MeasureTheory ProbabilityTheory Finset Fun Random


/--
Bessel's correction: the unbiased sample variance and the average squared deviation
from the true mean have the same expectation.

See [Bessel's correction](https://en.wikipedia.org/wiki/Bessel's_correction).
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ℕ → Ω → ℝ}
  {μ σ : ℝ}
  {n : ℕ}
-- given
  (h₀ : n ≥ 2)
  (h₁ : ∀ k : ℕ, PSpace π x[k])
  (h₂ : ∀ k : ℕ, MemLp x[k] 2 π)
  (h₃ : ∀ k : ℕ, x[k] ⟂ᵢ[π] x[:k])
  (h₄ : ∀ k : ℕ, 𝔼[x[k]: π](x[k]) = μ)
  (h₅ : ∀ k : ℕ, 𝕍𝕒𝕣[x[k]: π](x[k]) = σ²) :
-- imply
  have : PSpace π (Expectation.asRV x) := by
    simpa [Expectation.asRV_process] using
      PSpace_Path.of.All_PSpace (X := x) fun t => h₁ t
  𝔼[x: π]((∑ k ∈ range n, (x[k] - (∑ i ∈ range n, x[i]) / (n : ℝ))²) / ((n : ℝ) - 1)) =
    𝔼[x: π]((∑ k ∈ range n, (x[k] - μ)²) / (n : ℝ)) := by
-- proof
  intro hpath
  have hE : ∀ i : ℕ, ∫ ω, (x[i] ω) ∂π = μ := fun i => by
    have := h₁ i
    simpa [← Expect.eq.Integral, Expectation.asRV_function] using h₄ i
  have hvar : ∀ i : ℕ, variance x[i] π = σ² := fun i => by
    have := h₁ i
    rw [variance_eq_integral (PSpace.aemeasurable (x := x[i])), ← Var.eq.Integral]
    apply h₅ i
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.zero_lt_of_lt h₀).ne'
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < n := Nat.one_lt_cast.mpr (Nat.lt_of_succ_le h₀)
    linarith
  have hsq : ∀ i : ℕ, ∫ ω, (x[i] ω - μ)² ∂π = σ² := fun i => by
    have hv := variance_eq_integral (h₂ i).aemeasurable
    rw [hE i] at hv
    rw [← hv, hvar i]
  have hinterg : ∀ i : ℕ, Integrable (fun ω => (x[i] ω - μ)²) π := fun i =>
    ((h₂ i).sub (memLp_const μ)).integrable_sq
  have hsumμ : ∫ ω, ∑ k ∈ range n, (x[k] ω - μ)² ∂π = n * σ² := by
    rw [integral_finsetSum _ fun i _ => hinterg i,
      sum_congr rfl fun i _ => hsq i, sum_const, card_range, nsmul_eq_mul]
  have hfR :
    AEStronglyMeasurable
      (fun p : ℕ → ℝ => (∑ k ∈ range n, (p k - μ)²) / (n : ℝ))
      (π.map (Expectation.asRV x)) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have hR :
    𝔼[x: π]((∑ k ∈ range n, (x[k] - μ)²) / (n : ℝ)) = σ² := by
    change Expectation.ofRV π (Expectation.asRV x)
      (fun integ => (∑ k ∈ range n, (integ k - μ)²) / (n : ℝ)) = σ²
    rw [OfRV.eq.Integral.of.AEStronglyMeasurable_Map hfR]
    have hfun : (fun ω => (∑ k ∈ range n, (Expectation.asRV x ω k - μ)²) / (n : ℝ)) =
      fun ω => (∑ k ∈ range n, (x[k] ω - μ)²) / (n : ℝ) := by
      simp [getElem_nat_apply]
    rw [hfun]
    rw [integral_div, hsumμ]
    field_simp [hn0]
  have hpair : ∀ (i j : ℕ) (_ : i ≠ j), x[i] ⟂ᵢ[π] x[j] := by
    intro i j hij
    obtain hlt | hgt := Nat.lt_or_gt_of_ne hij
    ·
      have hx : (fun ω => x[:j] ω ⟨i, hlt⟩) = x[i] := by
        funext ω
        simp [Function.getSlice, FunSlice.slice, Int.toNat_zero]
      have hproj : x[j] ⟂ᵢ[π] (fun ω => x[:j] ω ⟨i, hlt⟩) :=
        (h₃ j).comp measurable_id (measurable_pi_apply _)
      simpa [hx] using hproj.symm
    ·
      have hx : (fun ω => x[:i] ω ⟨j, hgt⟩) = x[j] := by
        funext ω
        simp [Function.getSlice, FunSlice.slice, Int.toNat_zero]
      have hproj : x[i] ⟂ᵢ[π] (fun ω => x[:i] ω ⟨j, hgt⟩) :=
        (h₃ i).comp measurable_id (measurable_pi_apply _)
      simpa [hx] using hproj
  let avg : Ω → ℝ := fun ω => (∑ i ∈ range n, x[i] ω) / (n : ℝ)
  have hmem_avg : MemLp avg 2 π := by
    simpa [avg, Finset.sum_apply, div_eq_inv_mul] using
      (memLp_finsetSum' (range n) fun i _ => h₂ i).const_mul (n : ℝ)⁻¹
  have hmean : π[avg] = μ := by
    rw [integral_div, integral_finsetSum _ fun i _ => (h₂ i).integrable one_le_two,
      sum_congr rfl fun i _ => hE i, sum_const, card_range, nsmul_eq_mul]
    field_simp [hn0]
  have hvar_avg : variance avg π = σ² / (n : ℝ) := by
    rw [show avg = fun ω => (n : ℝ)⁻¹ * ∑ i ∈ range n, x[i] ω by
      ext ω
      simp [avg, div_eq_inv_mul]]
    rw [variance_const_mul,
      show (fun ω => ∑ i ∈ range n, x[i] ω) = ∑ i ∈ range n, x[i] from
        funext fun ω => (Finset.sum_apply ω (range n) (fun i => x[i])).symm,
      IndepFun.variance_sum (fun i _ => h₂ i) (fun i _ j _ hij => hpair i j hij),
      sum_congr rfl fun i _ => hvar i, sum_const, card_range, nsmul_eq_mul]
    field_simp [hn0]
  have havg_sq : ∫ ω, (avg ω - μ)² ∂π = σ² / (n : ℝ) := by
    have hv := variance_eq_integral hmem_avg.aemeasurable
    rw [hmean] at hv
    rw [← hv, hvar_avg]
  have hpoint : ∀ ω,
      ∑ k ∈ range n, (x[k] ω - avg ω)² =
        ∑ k ∈ range n, (x[k] ω - μ)² - (n : ℝ) * (avg ω - μ)² := by
    intro ω
    have hsum : ∑ k ∈ range n, (x[k] ω - μ) = (n : ℝ) * (avg ω - μ) := by
      simp [avg, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      field_simp [hn0]
    have hexp : ∀ k : ℕ, (x[k] ω - avg ω)² =
        (x[k] ω - μ)² - 2 * (avg ω - μ) * (x[k] ω - μ) + (avg ω - μ)² := by
      intro k
      ring
    simp_rw [hexp]
    rw [sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      ← mul_sum, hsum]
    ring
  have hinterg_avg : Integrable (fun ω => (avg ω - μ)²) π :=
    (hmem_avg.sub (memLp_const μ)).integrable_sq
  have hsum_dev : ∫ ω, ∑ k ∈ range n, (x[k] ω - avg ω)² ∂π = (n - 1 : ℝ) * σ² := by
    simp_rw [hpoint]
    rw [integral_sub, hsumμ, integral_const_mul, havg_sq]
    ·
      field_simp [hn0]
    · exact integrable_finsetSum _ fun i _ => hinterg i
    · exact hinterg_avg.const_mul _
  have hfL :
    AEStronglyMeasurable
      (fun p : ℕ → ℝ =>
        (∑ k ∈ range n, (p k - (∑ i ∈ range n, p i) / (n : ℝ))²) / ((n : ℝ) - 1))
      (π.map (Expectation.asRV x)) := by
    refine Continuous.aestronglyMeasurable ?_
    fun_prop
  have hL :
    𝔼[x: π]((∑ k ∈ range n, (x[k] - (∑ i ∈ range n, x[i]) / (n : ℝ))²) / ((n : ℝ) - 1)) =
      σ² := by
    change Expectation.ofRV π (Expectation.asRV x)
      (fun integ => (∑ k ∈ range n,
        (integ k - (∑ i ∈ range n, integ i) / (n : ℝ))²) / ((n : ℝ) - 1)) = σ²
    rw [OfRV.eq.Integral.of.AEStronglyMeasurable_Map hfL]
    have hfun : (fun ω => (∑ k ∈ range n,
        (Expectation.asRV x ω k - (∑ i ∈ range n, Expectation.asRV x ω i) / (n : ℝ))²) /
          ((n : ℝ) - 1)) =
      fun ω => (∑ k ∈ range n, (x[k] ω - avg ω)²) / ((n : ℝ) - 1) := by
      simp [getElem_nat_apply, avg]
    rw [hfun]
    rw [integral_div, hsum_dev]
    field_simp [hn1]
  rw [hL, hR]


-- created on 2023-10-08
-- updated on 2026-11-22
