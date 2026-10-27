import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal Topology

/--
[hasDerivAt_exp_half_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/GaussianFourthMoment.lean)
-/
@[path]
lemma hasDerivAt_exp_half_sq
  {t : ℝ} :
-- imply
  HasDerivAt (fun t => rexp (t ^ 2 / 2)) (t * rexp (t ^ 2 / 2)) t := by
-- proof
  have : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    have := (hasDerivAt_pow 2 t).div_const (2 : ℝ)
    simp at this
    exact this
  convert this.exp using 1
  ring

/--
[hasDerivAt_d1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/GaussianFourthMoment.lean)
-/
@[path]
lemma hasDerivAt_d1
  {t : ℝ} :
-- imply
  HasDerivAt (fun t => t * rexp (t ^ 2 / 2)) ((1 + t ^ 2) * rexp (t ^ 2 / 2)) t :=
-- proof
  ((hasDerivAt_id t).mul (hasDerivAt_exp_half_sq (t := t))).congr_deriv (by simp [id]; ring)

/--
[hasDerivAt_d2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/GaussianFourthMoment.lean)
-/
@[path]
lemma hasDerivAt_d2
  {t : ℝ} :
-- imply
  HasDerivAt (fun t => (1 + t ^ 2) * rexp (t ^ 2 / 2)) ((3 * t + t ^ 3) * rexp (t ^ 2 / 2)) t := by
-- proof
  have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t :=
    ((hasDerivAt_const t 1).add (hasDerivAt_pow 2 t)).congr_deriv (by push_cast; ring)
  exact (h1.mul (hasDerivAt_exp_half_sq (t := t))).congr_deriv (by ring)

/--
[hasDerivAt_d3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/GaussianFourthMoment.lean)
-/
@[path]
lemma hasDerivAt_d3
  {t : ℝ} :
-- imply
  HasDerivAt (fun t => (3 * t + t ^ 3) * rexp (t ^ 2 / 2))
    ((3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2)) t := by
-- proof
  have h1 : HasDerivAt (fun t : ℝ => 3 * t + t ^ 3) (3 + 3 * t ^ 2) t := by
    have hconst := (hasDerivAt_const t (3 : ℝ)).mul (hasDerivAt_id t)
    have hpow := hasDerivAt_pow 3 t
    exact (hconst.add hpow).congr_deriv (by push_cast; ring)
  exact (h1.mul (hasDerivAt_exp_half_sq (t := t))).congr_deriv (by
    simp only [add_mul, mul_assoc]
    ring)

/--
[deriv_four_exp_half_sq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/GaussianFourthMoment.lean)
-/
@[path]
lemma deriv_four_exp_half_sq_zero :
-- imply
  deriv^[4] (fun t : ℝ => rexp (t ^ 2 / 2)) 0 = 3 := by
-- proof
  have h0 : deriv (fun t : ℝ => rexp (t ^ 2 / 2)) =
      fun t => t * rexp (t ^ 2 / 2) :=
    funext fun t => (hasDerivAt_exp_half_sq (t := t)).deriv
  have h1 : deriv (fun t : ℝ => t * rexp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * rexp (t ^ 2 / 2) :=
    funext fun t => (hasDerivAt_d1 (t := t)).deriv
  have h2 : deriv (fun t : ℝ => (1 + t ^ 2) * rexp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * rexp (t ^ 2 / 2) :=
    funext fun t => (hasDerivAt_d2 (t := t)).deriv
  have h3 : deriv (fun t : ℝ => (3 * t + t ^ 3) * rexp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2) :=
    funext fun t => (hasDerivAt_d3 (t := t)).deriv
  simp [Function.iterate_succ_apply', h0, h1, h2, h3, exp_zero]

/--
[mgf_standard_gaussian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/GaussianFourthMoment.lean)
-/
@[path]
lemma mgf_standard_gaussian :
-- imply
  mgf id (gaussianReal (0 : ℝ) (1 : ℝ≥0)) = fun t => rexp (t ^ 2 / 2) := by
-- proof
  simpa using (mgf_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))

/--
[fourth_moment_standard_gaussian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/GaussianFourthMoment.lean)
-/
@[path]
lemma fourth_moment_standard_gaussian :
-- imply
  ∫ x, x ^ 4 ∂(gaussianReal (0 : ℝ) (1 : ℝ≥0)) = 3 := by
-- proof
  have h_int : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal (0 : ℝ) (1 : ℝ≥0))) := by
    rw [integrableExpSet_id_gaussianReal, interior_univ]
    trivial
  have h4 := iteratedDeriv_mgf_zero h_int 4
  simp only [Pi.pow_apply, id_eq] at h4
  rw [← h4, mgf_standard_gaussian]
  -- iteratedDeriv^[4] = deriv^[4] after unfolding
  simpa [iteratedDeriv_eq_iterate] using deriv_four_exp_half_sq_zero

/--
[abs_mul_four_le_sum_pow_four](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/GaussianFourthMoment.lean)
-/
@[path]
lemma abs_mul_four_le_sum_pow_four
  {a b c d : ℝ} :
-- imply
  |a * b * c * d| ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
-- proof
  have h1 : a * b * c * d ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (c ^ 2 - d ^ 2),
      sq_nonneg (a * b - c * d)]
  have h2 : -(a * b * c * d) ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (c ^ 2 - d ^ 2),
      sq_nonneg (a * b + c * d)]
  exact abs_le.mpr ⟨by linarith, h1⟩

/--
[product_bound_equidistributed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/GaussianFourthMoment.lean)
-/
@[path]
lemma product_bound_equidistributed
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {f : Fin 4 → Ω → ℝ}
-- given
  (hf_int : ∀ i, Integrable (fun ω => (f i ω) ^ 4) μ)
  (hf_equi : ∀ i, ∫ ω, (f i ω) ^ 4 ∂μ = ∫ ω, (f 0 ω) ^ 4 ∂μ)
  (hf_abs_int : Integrable (fun ω => |f 0 ω * f 1 ω * f 2 ω * f 3 ω|) μ) :
-- imply
  ∫ ω, |f 0 ω * f 1 ω * f 2 ω * f 3 ω| ∂μ ≤ ∫ ω, (f 0 ω) ^ 4 ∂μ := by
-- proof
  have h_sum_int : Integrable
      (fun ω => ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) / 4) μ :=
    (((hf_int 0).add (hf_int 1)).add (hf_int 2) |>.add (hf_int 3)).div_const 4
  have step1 :
      ∫ ω, |f 0 ω * f 1 ω * f 2 ω * f 3 ω| ∂μ ≤
        ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) / 4 ∂μ :=
    integral_mono hf_abs_int h_sum_int fun ω =>
      abs_mul_four_le_sum_pow_four (a := f 0 ω) (b := f 1 ω) (c := f 2 ω) (d := f 3 ω)
  have step2 :
      ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) / 4 ∂μ =
        ∫ ω, (f 0 ω) ^ 4 ∂μ := by
    have hdiv :=
      integral_div (f := fun ω =>
        (f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) (μ := μ) (r := (4 : ℝ))
    -- Prefer direct computation via additivity
    have h1 : ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4) ∂μ =
        ∫ ω, (f 0 ω) ^ 4 ∂μ + ∫ ω, (f 1 ω) ^ 4 ∂μ :=
      integral_add (hf_int 0) (hf_int 1)
    have h2 : ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4) ∂μ =
        ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4) ∂μ + ∫ ω, (f 2 ω) ^ 4 ∂μ :=
      integral_add ((hf_int 0).add (hf_int 1)) (hf_int 2)
    have h3 : ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) ∂μ =
        ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4) ∂μ + ∫ ω, (f 3 ω) ^ 4 ∂μ :=
      integral_add (((hf_int 0).add (hf_int 1)).add (hf_int 2)) (hf_int 3)
    have hsum :
        ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) ∂μ =
          4 * ∫ ω, (f 0 ω) ^ 4 ∂μ := by
      linarith [hf_equi 1, hf_equi 2, hf_equi 3, h1, h2, h3]
    calc ∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) / 4 ∂μ
        = (∫ ω, ((f 0 ω) ^ 4 + (f 1 ω) ^ 4 + (f 2 ω) ^ 4 + (f 3 ω) ^ 4) ∂μ) / 4 := by
            rw [integral_div]
      _ = (4 * ∫ ω, (f 0 ω) ^ 4 ∂μ) / 4 := by rw [hsum]
      _ = ∫ ω, (f 0 ω) ^ 4 ∂μ := by ring
  linarith

/--
[gaussian_fourth_moment_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/GaussianFourthMoment.lean)
-/
@[path]
lemma gaussian_fourth_moment_bound
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {f : Fin 4 → Ω → ℝ}
-- given
  (hf_int : ∀ i, Integrable (fun ω => (f i ω) ^ 4) μ)
  (hf_equi : ∀ i, ∫ ω, (f i ω) ^ 4 ∂μ = ∫ ω, (f 0 ω) ^ 4 ∂μ)
  (hf_abs_int : Integrable (fun ω => |f 0 ω * f 1 ω * f 2 ω * f 3 ω|) μ)
  (hf_gaussian : ∫ ω, (f 0 ω) ^ 4 ∂μ =
      ∫ x, x ^ 4 ∂(gaussianReal (0 : ℝ) (1 : ℝ≥0))) :
-- imply
  ∫ ω, |f 0 ω * f 1 ω * f 2 ω * f 3 ω| ∂μ ≤ 3 := by
-- proof
  have h_prod := product_bound_equidistributed hf_int hf_equi hf_abs_int
  have h_fourth := fourth_moment_standard_gaussian
  linarith


-- created on 2026-10-23
-- updated on 2026-10-26
