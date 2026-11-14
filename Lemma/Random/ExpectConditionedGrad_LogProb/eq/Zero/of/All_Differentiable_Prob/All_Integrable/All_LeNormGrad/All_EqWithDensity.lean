import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral_SMulProbFderiv_FunLog_Prob.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_EqWithDensity
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


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
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [DecidableEq 𝒮]
  [μ : ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {g : 𝒮 → 𝒜 → ℝ}
  {B : ℝ}
-- given
  (θ : Θ)
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : ∀ y u, Differentiable ℝ (fun θ => M.policy.prob θ y u))
  (h₂ : ∀ θ y u, ‖fderiv ℝ (fun θ => M.policy.prob θ y u) θ‖ ≤ g y u)
  (h₃ : ∀ y, Integrable (g y) μ.measure)
  (hφ : StronglyMeasurable
    (fun z : 𝒮 × 𝒜 => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hB : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ B)
  (t : ℕ)
  (x : 𝒮) :
-- imply
  ∫ ω, fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' x (a t ω))) θ
    ∂(M θ)[|s t ⁻¹' {x}] = 0 := by
-- proof
  have hS : MeasurableSet (s t ⁻¹' {x}) :=
    Random.Measurable.of.All_Eq.snd.fst h₀ t (measurableSet_singleton x)
  if hP : M θ (s t ⁻¹' {x}) = 0 then
    simp [cond_eq_zero_of_meas_eq_zero hP]
  else
    have hψ : StronglyMeasurable
        (Function.uncurry fun y u =>
          (if y = x then (1:ℝ) else 0) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ) := by
      have h' :=
        ((stronglyMeasurable_const (b := (1:ℝ))).indicator
          (measurableSet_singleton x)).comp_measurable measurable_fst |>.smul hφ
      convert h' using 1
      funext z
      by_cases hz : z.1 = x <;> simp [Function.uncurry, hz, Pi.single]
    have hψC : ∀ y u,
        ‖(if y = x then (1:ℝ) else 0) •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ B :=
      fun y u => by
        rw [norm_smul]
        have h1 : ‖(if y = x then (1:ℝ) else 0)‖ ≤ (1:ℝ) := by
          by_cases h : y = x <;> simp [h]
        calc
          ‖(if y = x then (1:ℝ) else 0)‖ * ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖
            ≤ 1 * B := mul_le_mul h1 (hB y u) (norm_nonneg _) zero_le_one
          _ = B := one_mul B
    rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hS]
    have hind :
        (fun ω => (s t ⁻¹' {x}).indicator
          (fun ω => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' x (a t ω))) θ) ω) =
          fun ω => (if s t ω = x then (1:ℝ) else 0) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ := by
      funext ω
      by_cases h : s t ω = x <;>
        simp [h, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
    rw [hind,
      Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity h₀ hψ hψC θ t]
    have hassoc : ∀ y u,
        M.policy.prob θ y u •
          ((if y = x then (1:ℝ) else 0) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ) =
          (if y = x then (1:ℝ) else 0) •
            (M.policy.prob θ y u •
              fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ) :=
      fun y u => by
        simp only [smul_smul, mul_comm (M.policy.prob θ y u)]
    simp_rw [hassoc]
    refine smul_eq_zero.2 (Or.inr ?_)
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    change ∫ u, (if y = x then (1:ℝ) else 0) •
        (M.policy.prob θ y u •
          fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ) ∂ReferenceMeasure.measure = 0
    rw [integral_smul,
      Integral_SMulProbFderiv_FunLog_Prob.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_EqWithDensity
        h₁ h₂ h₃ θ y,
      smul_zero]


-- created on 2023-04-03
