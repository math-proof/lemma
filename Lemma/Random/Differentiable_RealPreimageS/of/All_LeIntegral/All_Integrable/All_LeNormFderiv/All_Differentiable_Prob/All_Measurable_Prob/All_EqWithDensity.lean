import Def.Analysis.Calculus.Gradient.Operators
import Lemma.Random.RealPreimageS.eq.Sum_MulRealPn.of.All_EqWithDensity
import Lemma.Random.Differentiable.All_LeNormFderivMulAdd_1Mul_C.of.All_LeNorm.StronglyMeasurable.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
import Lemma.Real.StronglyMeasurable_Eq12
import Lemma.Real.Norm_Eq12.le.One
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
For a differentiable policy with an integrable gradient bound, `θ ↦ ℙ(s[t] = y)` is differentiable.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [DecidableEq 𝒮]
  [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {Cg : ℝ}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π[θ] z.1 z.2))
  (h₁ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₂ : ∀ sₜ, ∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖) ∂ReferenceMeasure.measure ≤ Cg)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) ReferenceMeasure.measure)
  (t : ℕ)
  (y : 𝒮) :
-- imply
  Differentiable ℝ (fun θ => (M θ).real (s t ⁻¹' {y})) := by
-- proof
  have e : (fun θ => (M θ).real (s t ⁻¹' {y})) =
      fun θ => ∑ x, M.init.toMeasure.real {x} *
        ∫ z, M.Kf θ (fun z => if z.2.1 = y then (1:ℝ) else 0) t z ∂(M.stageK θ x) :=
    funext fun θ =>
      RealPreimageS.eq.Sum_MulRealPn.of.All_EqWithDensity (M := M) h₀ θ t y
  rw [e]
  exact fun θ => DifferentiableAt.fun_sum fun x _ =>
    ((Differentiable.All_LeNormFderivMulAdd_1Mul_C.of.All_LeNorm.StronglyMeasurable.All_LeIntegral.All_Integrable.All_LeNormFderiv.All_Differentiable_Prob.All_Measurable_Prob
      (M := M) hπ h₁ h₂ hBdd hIntg (Real.StronglyMeasurable_Eq12 y) (Norm_Eq12.le.One y) zero_le_one t x).1 θ).const_mul _


-- created on 2026-11-13
-- updated on 2026-11-18