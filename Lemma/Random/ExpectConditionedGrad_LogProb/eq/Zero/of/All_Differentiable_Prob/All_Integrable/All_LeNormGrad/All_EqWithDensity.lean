import Def.Analysis.Calculus.Gradient.Operators.Part2
import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral_SMulProbFderiv_FunLog_Prob.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_EqWithDensity
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
Expected score of a density policy, conditioned on the state:
`𝔼[∇_θ log π_θ(a[t] | s[t]) | s[t] = x] = 0`.
Continuous-action counterpart of `Random.ExpectConditionedGrad_LogProb.eq.Zero`:
if `s[t] = x` is null then both sides vanish; otherwise rewrite the conditional
integral via disintegration and apply the zero-score identity
`∫ u, π_θ(u | x) • ∇ log π_θ(u | x) du = 0`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {B : ℝ}
-- given
  (θ : Θ)
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : ∀ y u, Differentiable ℝ (fun θ => M.π[θ] y u))
  (h₂ : ∀ y, Integrable (fun u => sSup (Set.range fun θ => ‖∇[θ] M.π[θ] y u‖)) μ.measure)
  (hBdd : ∀ y u, BddAbove (Set.range fun θ => ‖∇[θ] M.π[θ] y u‖))
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.π[θ'] z.1 z.2)) θ))
  (hB : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ‖ ≤ B)
  (t : ℕ)
  (sₜ : 𝒮) :
-- imply
  ∫ ω, fderiv ℝ (fun θ' => Real.log (M.π[θ'] sₜ (a t ω))) θ
    ∂(M.traj θ)[|s t ⁻¹' {sₜ}] = 0 := by
-- proof
  have hS : MeasurableSet (s t ⁻¹' {sₜ}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton sₜ)
  if hP : M.traj θ (s t ⁻¹' {sₜ}) = 0 then
    simp [cond_eq_zero_of_meas_eq_zero hP]
  else
    have hψ : StronglyMeasurable
        (Function.uncurry fun y u =>
          (if y = sₜ then (1:ℝ) else 0) •
            fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ) := by
      have h' :=
        ((stronglyMeasurable_const (b := (1:ℝ))).indicator
          (measurableSet_singleton sₜ)).comp_measurable measurable_fst |>.smul hφ
      convert h' using 1
      funext z
      by_cases hz : z.1 = sₜ <;> simp [Function.uncurry, hz, Pi.single]
    have hψC : ∀ y u,
        ‖(if y = sₜ then (1:ℝ) else 0) •
          fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ‖ ≤ B :=
      fun y u => by
        rw [norm_smul]
        have h1 : ‖(if y = sₜ then (1:ℝ) else 0)‖ ≤ (1:ℝ) := by
          by_cases h : y = sₜ <;> simp [h]
        calc
          ‖(if y = sₜ then (1:ℝ) else 0)‖ * ‖fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ‖
            ≤ 1 * B := mul_le_mul h1 (hB y u) (norm_nonneg _) zero_le_one
          _ = B := one_mul B
    rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hS]
    have hind :
        (fun ω => (s t ⁻¹' {sₜ}).indicator
          (fun ω => fderiv ℝ (fun θ' => Real.log (M.π[θ'] sₜ (a t ω))) θ) ω) =
          fun ω => (if s t ω = sₜ then (1:ℝ) else 0) •
            fderiv ℝ (fun θ' => Real.log (M.π[θ'] (s t ω) (a t ω))) θ := by
      funext ω
      by_cases h : s t ω = sₜ <;>
        simp [h, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    rw [hind,
      Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity h₀ hψ hψC θ t]
    have hassoc : ∀ y u,
        M.π[θ] y u •
          ((if y = sₜ then (1:ℝ) else 0) •
            fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ) =
          (if y = sₜ then (1:ℝ) else 0) •
            (M.π[θ] y u •
              fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ) :=
      fun y u => by
        simp only [smul_smul, mul_comm (M.π[θ] y u)]
    simp_rw [hassoc]
    refine smul_eq_zero.2 (Or.inr ?_)
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    change ∫ u, (if y = sₜ then (1:ℝ) else 0) •
        (M.π[θ] y u •
          fderiv ℝ (fun θ' => Real.log (M.π[θ'] y u)) θ) ∂ReferenceMeasure.measure = 0
    rw [integral_smul,
      Integral_SMulProbFderiv_FunLog_Prob.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_EqWithDensity
        h₁ h₂ hBdd θ y,
      smul_zero]


-- created on 2023-04-03
-- updated on 2026-11-16
