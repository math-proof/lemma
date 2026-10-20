import Lemma.Random.Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Integral_SMulProbFderiv_FunLog_Prob.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_EqWithDensity
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


/--
`𝔼[h(s[t]) • ∇ log π(a[t] | s[t])] = 0` for a density policy.
Continuous-action counterpart of
`Random.Integral_SMul.eq.Zero.of.All_Differentiable_Prob`:
rewrite via the continuous `Integral.eq.Sum_Sum_SMul` analogue, then apply the continuous
zero-score identity.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  {g : S → A → ℝ}
  {C B : ℝ}
-- given
  (θ : Θ)
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₂ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₃ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h : S → ℝ)
  (hh : Measurable h)
  (hC : ∀ y, ‖h y‖ ≤ C)
  (hφ : StronglyMeasurable
    (fun z : S × A => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hB : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ B)
  (t : ℕ) :
-- imply
  ∫ ω, h (s t ω) • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ
    ∂(M θ) = 0 := by
-- proof
  have hφm : StronglyMeasurable
    (Function.uncurry fun y u => h y •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ) :=
    (hh.comp measurable_fst).stronglyMeasurable.smul hφ
  have hφC : ∀ y u,
    ‖h y • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ C * B :=
    fun y u => by
      rw [norm_smul]
      exact mul_le_mul (hC y) (hB y u) (norm_nonneg _) ((norm_nonneg _).trans (hC y))
  rw [Integral.eq.Integral_Integral_SMul.of.All_Eq_Joint.All_EqWithDensity h₀ hφm hφC θ t]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  have hassoc : ∀ u,
      M.policy.prob θ y u •
        (h y • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ) =
      h y • (M.policy.prob θ y u •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ) :=
    fun u => by
      simp only [smul_smul, mul_comm (M.policy.prob θ y u)]
  simp_rw [hassoc]
  rw [integral_smul,
    Integral_SMulProbFderiv_FunLog_Prob.eq.Zero.of.All_Differentiable_Prob.All_Integrable.All_LeNormGrad.All_EqWithDensity
      h₁ h₂ h₃ θ y,
    smul_zero]
  rfl


-- created on 2026-10-20
