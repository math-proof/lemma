import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb.All_EqWithDensity
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
`𝔼[g(s[t], a[t]) • ∇ log π(a[t] | s[t])]
  = ∫ y, (∫ u, g y u • ∇π_θ(u | y) du) ∂law(s[t])`
for a density policy.
Continuous-action counterpart of
`Random.Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob`:
rewrite via the continuous `Integral.eq.Sum_Sum_SMul` analogue, then apply
`π • ∇ log π = ∇π`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
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
  (g : 𝒮 → 𝒜 → ℝ)
  (hg : StronglyMeasurable (Function.uncurry g))
  (hC : ∀ y u, ‖g y u‖ ≤ C)
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.π[θ'] z.1 z.2)) θ))
  (hB : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ‖ ≤ B)
  (t : ℕ) :
-- imply
  ∫ ω, g (s t ω) (a t ω) • fderiv ℝ (fun θ' => Real.log (M.π[θ'] (s t ω) (a t ω))) θ
    ∂(M.traj θ) =
    ∫ y, (∫ u, g y u • fderiv ℝ (fun θ' => M.π[θ'] y u) θ ∂μ.measure)
      ∂((M.traj θ).map (s t)) := by
-- proof
  have hφm : StronglyMeasurable
    (Function.uncurry fun y u => g y u •
      fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ) :=
    hg.smul hφ
  have hφC : ∀ y u,
    ‖g y u • fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ‖ ≤ C * B :=
    fun y u => by
      rw [norm_smul]
      exact mul_le_mul (hC y u) (hB y u) (norm_nonneg _) ((norm_nonneg _).trans (hC y u))
  rw [Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity h₀ hφm hφC θ t]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hassoc : ∀ u,
      M.π[θ] y u •
        (g y u • fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ) =
      g y u • fderiv ℝ (fun θ' => M.π[θ'] y u) θ :=
    fun u => by
      have hswap :
          M.π[θ] y u •
            (g y u • fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ) =
          g y u • (M.π[θ] y u •
            fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ) := by
        simp only [smul_smul, mul_comm (M.π[θ] y u)]
      rw [hswap,
        EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb.All_EqWithDensity
          (M := M) h₁ θ y u]
  simp_rw [hassoc]


-- created on 2026-11-14
-- updated on 2026-11-17
