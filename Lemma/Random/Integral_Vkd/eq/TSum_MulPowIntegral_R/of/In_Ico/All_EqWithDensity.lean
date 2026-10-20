import Lemma.Random.Integral_R.eq.Integral_Wkd.of.All_Eq.All_EqWithDensity
import Lemma.Random.NormWkd.le.Abs_R
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Real


/--
The init-average of `Vkd` is the discounted expected path return:
`∫ Vkd θ γ ∂init = ∑' t, γ ^ t * ∫ r[t]`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (θ : Θ) :
-- imply
  ∫ x, M.Vkd θ γ x ∂M.env.init =
    ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ) := by
-- proof
  have := M.env.init_prob
  have hW : ∀ t, ∫ ω, r t ω ∂(M θ) =
    ∫ x, M.Wkd θ t x ∂M.env.init := fun t =>
    Integral_R.eq.Integral_Wkd.of.All_Eq.All_EqWithDensity (M := M) h₁ θ t
  simp_rw [hW]
  have hmeas : ∀ t, Measurable (M.Wkd θ t) := fun t =>
    Measurable_Wkd.of.All_Measurable_Prob hπ θ t
  have hbd : ∀ t x, ‖M.Wkd θ t x‖ ≤ |M.env.R| := fun t x =>
    NormWkd.le.Abs_R (M := M) θ t x
  have hri : ∀ t, Integrable (fun x => γ ^ t * M.Wkd θ t x) M.env.init :=
    fun t => by
      refine Integrable.of_bound ((hmeas t).const_mul (γ ^ t)).aestronglyMeasurable
        (γ ^ t * |M.env.R|) ?_
      filter_upwards with x
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left (hbd t x) (pow_nonneg h₀.1 t)
  have hsum_norm :
    Summable (fun t => ∫ x, ‖γ ^ t * M.Wkd θ t x‖ ∂M.env.init) := by
    refine Summable.of_nonneg_of_le
      (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
    calc
      _ ≤ ∫ _, γ ^ t * |M.env.R| ∂M.env.init :=
        integral_mono_ae (hri t).norm (integrable_const _)
          (Filter.Eventually.of_forall fun x => by
            change ‖γ ^ t * M.Wkd θ t x‖ ≤ γ ^ t * |M.env.R|
            rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
            exact mul_le_mul_of_nonneg_left (hbd t x) (pow_nonneg h₀.1 t))
      _ = γ ^ t * |M.env.R| := by simp
  have hswap :
    ∫ x, ∑' t, γ ^ t * M.Wkd θ t x ∂M.env.init =
      ∑' t, ∫ x, γ ^ t * M.Wkd θ t x ∂M.env.init :=
    (integral_tsum_of_summable_integral_norm hri hsum_norm).symm
  have hV : (fun x => M.Vkd θ γ x) =
    fun x => ∑' t, γ ^ t * M.Wkd θ t x := funext fun x => rfl
  rw [hV, hswap]
  refine tsum_congr fun t => ?_
  exact integral_const_mul _ _


-- created on 2026-10-20
