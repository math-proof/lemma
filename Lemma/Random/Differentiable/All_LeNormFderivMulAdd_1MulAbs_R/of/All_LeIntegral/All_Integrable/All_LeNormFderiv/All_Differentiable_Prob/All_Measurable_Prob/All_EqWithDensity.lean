import Def.Analysis.Calculus.Gradient.Operators.Part2
import Mathlib.Analysis.Calculus.ParametricIntegral
import Lemma.Random.Integral_R.eq.Integral_Wkd.of.All_Eq.All_EqWithDensity
import Lemma.Random.Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
import Lemma.Random.Measurable_Wkd.of.All_Measurable_Prob
import Lemma.Random.NormWkd.le.Abs_R
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
For a differentiable density policy with `‖∇π‖ ≤ g` and `∫ g ≤ Cg`, the path reward
`θ ↦ ∫ r[t]` is differentiable with derivative bound `(t + 1) * (Cg * |R|)`.
Continuous-action counterpart of
`Random.Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {Cg : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (h₁ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₂ : ∀ sₜ, ∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂μ.measure ≤ Cg)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) μ.measure)
  (t : ℕ) :
-- imply
  Differentiable ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) ∧
    ∀ θ, ‖fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) θ‖ ≤
    (t + 1) * (Cg * |M.R|) := by
-- proof
  have e : (fun θ => ∫ ω, r t ω ∂(M.traj θ)) =
      fun θ => ∫ x, M.Wkd θ t x ∂(M.init : Measure _) :=
    funext fun θ =>
      Integral_R.eq.Integral_Wkd.of.All_Eq.All_EqWithDensity (M := M) h₀ θ t
  rw [e]
  have hW :=
    Differentiable.All_LeNormFderivMulAdd_1MulAbs_R.of.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
      (M := M) hπ h₁ h₂ hBdd hIntg t
  have hmeas : ∀ θ, Measurable (M.Wkd θ t) := fun θ =>
    Measurable_Wkd.of.All_Measurable_Prob hπ θ t
  have hbd : ∀ θ x, ‖M.Wkd θ t x‖ ≤ |M.R| := fun θ x =>
    NormWkd.le.Abs_R (M := M) θ t x
  have hF : ∀ θ, HasFDerivAt (fun θ => ∫ x, M.Wkd θ t x ∂(M.init : Measure _))
      (∫ x, fderiv ℝ (fun θ => M.Wkd θ t x) θ ∂(M.init : Measure _)) θ := fun θ =>
    hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun θ x => M.Wkd θ t x)
      (F' := fun θ x => fderiv ℝ (fun θ => M.Wkd θ t x) θ) (s := Set.univ)
      (bound := fun _ => ((t : ℝ) + 1) * (Cg * |M.R|)) Filter.univ_mem
      (Filter.Eventually.of_forall fun θ' => (hmeas θ').aestronglyMeasurable)
      (Integrable.of_bound (hmeas θ).aestronglyMeasurable |M.R|
        (Filter.Eventually.of_forall fun x => hbd θ x))
      (StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
        hmeas (fun x => (hW x).1 θ)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x θ' _ => (hW x).2 θ')
      (integrable_const _)
      (Filter.Eventually.of_forall fun x θ' _ => ((hW x).1 θ').hasFDerivAt)
  refine ⟨fun θ => (hF θ).differentiableAt, fun θ => ?_⟩
  rw [(hF θ).fderiv]
  have h := norm_integral_le_of_norm_le_const (μ := (M.init : Measure _))
    (Filter.Eventually.of_forall fun x => (hW x).2 θ)
  simpa using h


-- created on 2026-10-20
-- updated on 2026-11-17