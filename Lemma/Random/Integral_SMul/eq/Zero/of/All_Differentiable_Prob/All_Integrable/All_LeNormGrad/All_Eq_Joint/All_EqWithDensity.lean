import Def.Analysis.Calculus.Gradient.Operators.Part2
import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral_SMulProbFderiv_FunLog_Prob.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_EqWithDensity
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
`𝔼[h(s[t]) • ∇ log π(a[t] | s[t])] = 0` for a density policy.
Continuous-action counterpart of
`Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob`:
rewrite via the continuous `Integral.eq.Sum_Sum_SMul` analogue, then apply the continuous
zero-score identity.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {C B : ℝ}
-- given
  (θ : Θ)
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π[θ] sₜ aₜ))
  (h₂ : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖)) μ.measure)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] sₜ aₜ‖))
  (h : 𝒮 → ℝ)
  (hh : Measurable h)
  (hC : ∀ y, ‖h y‖ ≤ C)
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.π[θ'] z.1 z.2)) θ))
  (hB : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ‖ ≤ B)
  (t : ℕ) :
-- imply
  ∫ ω, h (s t ω) • fderiv ℝ (fun θ' => Real.log (M.π[θ'] (s t ω) (a t ω))) θ
    ∂(M.traj θ) = 0 := by
-- proof
  have hφm : StronglyMeasurable
    (Function.uncurry fun y u => h y •
      fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ) :=
    (hh.comp measurable_fst).stronglyMeasurable.smul hφ
  have hφC : ∀ y u,
    ‖h y • fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ‖ ≤ C * B :=
    fun y u => by
      rw [norm_smul]
      exact mul_le_mul (hC y) (hB y u) (norm_nonneg _) ((norm_nonneg _).trans (hC y))
  rw [Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity h₀ hφm hφC θ t]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  have hassoc : ∀ u,
      M.π[θ] y u •
        (h y • fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ) =
      h y • (M.π[θ] y u •
        fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ) :=
    fun u => by
      simp only [smul_smul, mul_comm (M.π[θ] y u)]
  simp_rw [hassoc]
  rw [integral_smul,
    Integral_SMulProbFderiv_FunLog_Prob.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_EqWithDensity
      h₁ h₂ hBdd θ y,
    smul_zero]
  rfl


-- created on 2026-10-20
-- updated on 2026-11-17