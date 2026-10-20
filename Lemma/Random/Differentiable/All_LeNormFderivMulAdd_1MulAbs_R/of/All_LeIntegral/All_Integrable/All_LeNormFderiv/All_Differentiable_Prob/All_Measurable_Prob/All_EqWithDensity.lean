import Mathlib.Analysis.Calculus.ParametricIntegral
import Lemma.Random.Integral_R.eq.Integral_Wkd.of.All_Eq.All_EqWithDensity
import Lemma.Random.Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Random.NormWkd.le.Abs_R
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random Real


/--
For a differentiable density policy with `‖∇π‖ ≤ g` and `∫ g ≤ Cg`, the path reward
`θ ↦ ∫ r[t]` is differentiable with derivative bound `(t + 1) * (Cg * |R|)`.
Continuous-action counterpart of
`Random.Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {g : S → A → ℝ}
  {Cg : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₂ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₃ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₄ : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg)
  (t : ℕ) :
-- imply
  Differentiable ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) ∧
    ∀ θ, ‖fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ‖ ≤
    (t + 1) * (Cg * |M.env.R|) := by
-- proof
  have := M.env.init_prob
  have e : (fun θ => ∫ ω, r t ω ∂(M θ)) =
      fun θ => ∫ x, M.Wkd θ t x ∂M.env.init :=
    funext fun θ =>
      Integral_R.eq.Integral_Wkd.of.All_Eq.All_EqWithDensity (M := M) h₀ θ t
  rw [e]
  have hW :=
    Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
      (M := M) hπ h₁ h₂ h₃ h₄ t
  have hmeas : ∀ θ, Measurable (M.Wkd θ t) := fun θ =>
    Measurable_Wkd.of.All_Measurable_Prob hπ θ t
  have hbd : ∀ θ x, ‖M.Wkd θ t x‖ ≤ |M.env.R| := fun θ x =>
    NormWkd.le.Abs_R (M := M) θ t x
  have hF : ∀ θ, HasFDerivAt (fun θ => ∫ x, M.Wkd θ t x ∂M.env.init)
      (∫ x, fderiv ℝ (fun θ => M.Wkd θ t x) θ ∂M.env.init) θ := fun θ =>
    hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun θ x => M.Wkd θ t x)
      (F' := fun θ x => fderiv ℝ (fun θ => M.Wkd θ t x) θ) (s := Set.univ)
      (bound := fun _ => ((t : ℝ) + 1) * (Cg * |M.env.R|)) Filter.univ_mem
      (Filter.Eventually.of_forall fun θ' => (hmeas θ').aestronglyMeasurable)
      (Integrable.of_bound (hmeas θ).aestronglyMeasurable |M.env.R|
        (Filter.Eventually.of_forall fun x => hbd θ x))
      (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
        hmeas (fun x => (hW x).1 θ)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x θ' _ => (hW x).2 θ')
      (integrable_const _)
      (Filter.Eventually.of_forall fun x θ' _ => ((hW x).1 θ').hasFDerivAt)
  refine ⟨fun θ => (hF θ).differentiableAt, fun θ => ?_⟩
  rw [(hF θ).fderiv]
  have h := norm_integral_le_of_norm_le_const (μ := M.env.init)
    (Filter.Eventually.of_forall fun x => (hW x).2 θ)
  simpa using h


-- created on 2026-10-20
