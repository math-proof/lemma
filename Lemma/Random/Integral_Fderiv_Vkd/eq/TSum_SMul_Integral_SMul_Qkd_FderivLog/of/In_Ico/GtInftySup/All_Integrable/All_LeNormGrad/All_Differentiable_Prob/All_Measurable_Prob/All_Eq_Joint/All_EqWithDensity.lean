import sympy.concrete.sup
import Lemma.Random.Integral_Fderiv_Vkd.eq.Add_SMul_Integral_SMul_FderivLog.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.Map.eq.Init.of.All_Eq_Joint.All_EqWithDensity
import Lemma.Random.GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Real.Eq_0.Lim.of.LtAbs.GtInftySup
import Lemma.Random.Measurable_Qkd.of.All_Measurable_Prob
import Lemma.Random.NormVkd.le.MulInvSub1Abs_R.of.In_Ico
import Lemma.Random.NormRkd.le.Abs_R
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Filter Random Real
set_option maxHeartbeats 800000


/--
Finite-horizon policy-gradient unroll under the continuous path law.
-/
private lemma finite
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {g : S → A → ℝ}
  {Cg Ms : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₄ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₅ : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg)
  (hφ : StronglyMeasurable
    (fun z : S × A => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms)
  (n : ℕ) :
  ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s 0)) =
    ∑ t ∈ Finset.range n, γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
      γ ^ n • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s n)) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hstep :=
      Integral_Fderiv_Vkd.eq.Add_SMul_Integral_SMul_FderivLog.of.All_Eq_Joint.All_EqWithDensity
        (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ hφ hMs n
    calc
      _ = ∑ t ∈ Finset.range n, γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
          γ ^ n • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s n)) := ih
      _ = ∑ t ∈ Finset.range n, γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
          γ ^ n • (∫ ω, M.Qkd θ γ (s n ω) (a n ω) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s n ω) (a n ω))) θ ∂(M θ) +
            γ • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s (n + 1)))) := by
        rw [hstep]
      _ = ∑ t ∈ Finset.range (n + 1), γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
            fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
          γ ^ (n + 1) • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s (n + 1))) := by
        simp only [Finset.sum_range_succ, smul_add, smul_smul, pow_succ]
        abel

/--
Infinite-horizon policy-gradient identity: path integral of `∇Vkd` at `init` equals the
discounted Q-score series.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {g : S → A → ℝ}
  {Cg Ms : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hπ : ∀ θ, Measurable (fun z : S × A => M.policy.prob θ z.1 z.2))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₃ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₄ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₅ : ∀ x, ∫ u, g x u ∂ReferenceMeasure.measure ≤ Cg)
  (hφ : StronglyMeasurable
    (fun z : S × A => fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' z.1 z.2)) θ))
  (hMs : ∀ y u, ‖fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' y u)) θ‖ ≤ Ms) :
-- imply
  ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂M.env.init =
    ∑' t, γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
      fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
-- proof
  classical
  have := M.env.init_prob
  have := M.env.trans_markov
  have hgrad : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u :=
    fun θ x u => by simpa [gradient, LinearIsometryEquiv.norm_map] using h₃ θ x u
  have hsup : sup[x] ∫ u, g x u ∂ReferenceMeasure.measure < ∞ :=
    ⟨Cg, by rintro _ ⟨x, rfl⟩; exact h₅ x⟩
  obtain ⟨C, hC⟩ :=
    GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
      (M := M) h₂ hgrad h₄ hsup h₀ hπ
  have hCb : ∀ y, ‖fderiv ℝ (fun θ => M.Vkd θ γ y) θ‖ ≤ C := fun y => by
    have h := hC ⟨(θ, y), rfl⟩
    simpa [gradient, LinearIsometryEquiv.norm_map] using h
  have hinit := Map.eq.Init.of.All_Eq_Joint.All_EqWithDensity (M := M) h₁ θ
  set BQ : ℝ := |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|)
  have hQb : ∀ x u, ‖M.Qkd θ γ x u‖ ≤ BQ := fun x u => by
    have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u))
      (Filter.Eventually.of_forall fun y => NormVkd.le.MulInvSub1Abs_R.of.In_Ico (M := M) h₀ θ y)
    unfold DensityModel.Qkd
    refine (norm_add_le _ _).trans (add_le_add (NormRkd.le.Abs_R (M := M) x u) ?_)
    rw [norm_mul, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (by simpa using h) h₀.1
  have hscore_bd : ∀ t,
    ‖∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ)‖ ≤
        BQ * Ms := fun t => by
    have : IsProbabilityMeasure (M θ) := inferInstance
    refine (norm_integral_le_of_norm_le_const (μ := M θ)
      (Filter.Eventually.of_forall fun ω => by
        rw [norm_smul]
        exact mul_le_mul (hQb (s t ω) (a t ω)) (hMs (s t ω) (a t ω)) (norm_nonneg _)
          ((norm_nonneg _).trans (hQb (s t ω) (a t ω))))).trans_eq (by simp)
  have hsum :
    Summable fun t => γ ^ t • ∫ ω, M.Qkd θ γ (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (BQ * Ms)) fun t => ?_
    rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (hscore_bd t) (pow_nonneg h₀.1 t)
  have hrem : Tendsto
    (fun n => γ ^ n • ∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s n)))
      atTop (𝓝 0) := by
    have hγ : |γ| < 1 := (abs_of_nonneg h₀.1).symm ▸ h₀.2
    have hbd : ∀ n, ‖∫ x, fderiv ℝ (fun θ => M.Vkd θ γ x) θ ∂((M θ).map (s n))‖ ≤ C :=
      fun n => by
        have : IsProbabilityMeasure ((M θ).map (s n)) := inferInstance
        exact (norm_integral_le_of_norm_le_const
          (Filter.Eventually.of_forall hCb)).trans_eq (by simp)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (Eq_0.Lim.of.LtAbs.GtInftySup hγ
      ⟨C, by rintro _ ⟨n, rfl⟩; exact (abs_norm _).trans_le (hbd n)⟩).congr fun n => ?_
    rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
  have hfin := fun n =>
    finite (M := M) h₀ h₁ hπ h₂ h₃ h₄ h₅ hφ hMs n
  refine tendsto_nhds_unique
    (tendsto_const_nhds.congr fun n => ?_)
    ((hsum.hasSum.tendsto_sum_nat.add hrem).trans (by rw [add_zero]))
  rw [hinit.symm, hfin n, add_comm]


-- created on 2026-10-20
