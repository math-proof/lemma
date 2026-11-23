import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Real.NormIntegral.le.of.All_LeNormMul.EqIntegral_1
open MeasureTheory PolicyGradient Random Real


/--
The `k`-step expected reward with a density policy is bounded: `‖Wkd θ k x‖ = ‖𝔼[r[t+k] | s[t] = x]‖ ≤ |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy]
-- given
  (R : ℝ)
  (θ : Θ)
  (k : ℕ)
  (sₜ : 𝒮) :
-- imply
  ‖M.Wkd R θ k sₜ‖ ≤ |R| := by
-- proof
  induction k generalizing sₜ with
  | zero =>
    apply NormIntegral.le.of.All_LeNormMul.EqIntegral_1 (hStoch.integral_eq_one θ sₜ)
    intro u
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |M.π θ sₜ u| * |M.rkd R sₜ u|
          = M.π θ sₜ u * |M.rkd R sₜ u| := by
        congr 1
        exact abs_of_nonneg (hStoch.nonneg θ sₜ u)
      _ ≤ M.π θ sₜ u * |R| :=
        mul_le_mul_of_nonneg_left (NormRkd.le.Abs_R (M := M) R sₜ u) (hStoch.nonneg θ sₜ u)
  | succ k ih =>
    apply NormIntegral.le.of.All_LeNormMul.EqIntegral_1 (hStoch.integral_eq_one θ sₜ)
    intro u
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |M.π θ sₜ u| * |∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, u))|
          = M.π θ sₜ u * |∫ y, M.Wkd R θ k y ∂(M.trans (sₜ, u))| := by
        congr 1
        exact abs_of_nonneg (hStoch.nonneg θ sₜ u)
      _ ≤ M.π θ sₜ u * |R| := by
        apply mul_le_mul_of_nonneg_left _ (hStoch.nonneg θ sₜ u)
        simpa using
          norm_integral_le_of_norm_le_const (μ := M.trans (sₜ, u))
            (Filter.Eventually.of_forall fun y => ih y)


-- created on 2026-10-07
-- updated on 2026-11-18
