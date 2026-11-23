import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Prod
import Lemma.Random.Fderiv.eq.AddIntegral_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
open MeasureTheory PolicyGradient Random Real


/--
Policy-gradient recursion with a continuous state space and a continuous action space:
∇V(s[t] = s.bvar[t]) = ∫ u, (rkd + γ * ∫ V0)(s.bvar[t], u) • ∇π(u | s.bvar[t]) du + γ • ∫ y, ℙ(s[t+1] = y | s[t] = s.bvar[t]) • ∇V(s[t+1] = y) dy,
the gradient of the Bellman equations of extract_QVA; both the action sum and the next-state sum of the corresponding discrete-state, discrete-action recursion
become integrals against the reference measures of `𝒜` and `𝒮` (e.g. Lebesgue measures on `ℝ^m`, `ℝ^b`).
The policy `π_θ(u | x)` is a probability density w.r.t. the reference measure of `𝒜` (`Policy`); `V = V0` is
the discounted `Wkd` series, defined on all states (see `Def.Dynamics.PolicyTrajectory.ContinuousAction`);
the action-value in the first integral is the closed form `rkd + γ * ∫ V0 ∂T`, so no reachability hypothesis is needed;
`ℙ(s[t+1] = y | s[t] = x) = P1kd θ p x y = ∫ u, π_θ(u | x) * p x u y du`.
h₁: θ ↦ π_θ(u | x) is differentiable; h₂, h₃, h₄: its gradient is dominated by `g x u`, where `g x` is integrable over
the actions uniformly in the state (this replaces `sup ‖∇π‖ < ∞` of the finite-action version, where `∑ u` is
integration against the counting measure); h₅: (x, u) ↦ π_θ(u | x) is jointly measurable; h₆, h₇, h₈: `p x u` is a
nonnegative density of the transition `T(· | x, u)` w.r.t. the reference measure of `𝒮`, jointly measurable in the
action and the next state (for Fubini).
`Θ` is finite-dimensional (the weights `π` have shape `(D,)`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [μ : ReferenceMeasure 𝒮] [MeasurableSingletonClass 𝒮]
  [ν : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {«\sf{s}» : ℕ → 𝒮}
  {p : 𝒮 → 𝒜 → 𝒮 → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π θ sₜ aₜ))
  (h₂ : sup[sₜ] (∫ aₜ, sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖) ∂ν.measure) < ∞)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖))
  (hIntg : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖)) ν.measure)
  (h₅ : ∀ θ, Measurable (fun z : 𝒮 × 𝒜 => M.π θ z.1 z.2))
  (h₆ : ∀ x, Measurable (fun z : 𝒜 × 𝒮 => p x z.1 z.2))
  (h₇ : ∀ x u y, p x u y ≥ 0)
  (h₈ : ∀ x u, M.trans (x, u) = (μ.measure : Measure 𝒮).withDensity (fun y => ENNReal.ofReal (p x u y)))
  (R : ℝ) :
-- imply
  ∇[θ] M.V0 R θ γ («\sf{s}» t) =
    ∫ u, ((M.rkd R («\sf{s}» t) u + γ * ∫ y, M.V0 R θ γ y ∂(M.trans («\sf{s}» t, u))) •
        ∇[θ] M.π θ («\sf{s}» t) u) ∂ν.measure +
      γ • ∫ y, (M.P1kd θ p («\sf{s}» t) y • ∇[θ] M.V0 R θ γ y) ∂μ.measure := by
-- proof
  set sₜ := «\sf{s}» t
  have hF := bellmanFderivClosed (M := M) (R := R) h₁ h₂ hBdd hIntg h₀ h₅ sₜ θ
  obtain ⟨C, hC⟩ := GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₁ h₂ hBdd hIntg h₀ h₅ R
  have hCb : ∀ y, ‖fderiv ℝ (fun θ => M.V0 R θ γ y) θ‖ ≤ C := fun y => by
    have h := hC ⟨(θ, y), rfl⟩
    simpa [gradient, LinearIsometryEquiv.norm_map] using h
  have hgm : StronglyMeasurable (fun y => fderiv ℝ (fun θ => M.V0 R θ γ y) θ) :=
    StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
      (fun θ' => Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ R θ' γ)
      (fun y => (HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₁ h₂ hBdd hIntg h₀ h₅ R y θ).differentiableAt)
  have hπ : Integrable (M.π θ sₜ) ReferenceMeasure.measure :=
    Integrable.of_integral_ne_zero (by
      have h1 : ∫ a, M.π θ sₜ a ∂ν.measure = 1 :=
        hStoch.integral_eq_one θ sₜ
      rw [h1]
      apply one_ne_zero)
  have hπm : Measurable (M.π θ sₜ) := (h₅ θ).comp measurable_prodMk_left
  have hp : ∀ u, Measurable (p sₜ u) := fun u => (h₆ sₜ).comp measurable_prodMk_left
  have hd : ∀ u, ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (sₜ, u)) =
      ∫ y, p sₜ u y • fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂ReferenceMeasure.measure := fun u => by
    rw [h₈, integral_withDensity_eq_integral_toReal_smul (hp u).ennreal_ofReal
      (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (h₇ sₜ u _)]
  have hi : ∀ u, Integrable (fun y => p sₜ u y • fderiv ℝ (fun θ => M.V0 R θ γ y) θ) ReferenceMeasure.measure := fun u => by
    have hI : Integrable (fun y => fderiv ℝ (fun θ => M.V0 R θ γ y) θ) (M.trans (sₜ, u)) :=
      Integrable.of_bound hgm.aestronglyMeasurable C (Filter.Eventually.of_forall hCb)
    rw [h₈, integrable_withDensity_iff_integrable_smul' (hp u).ennreal_ofReal
      (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)] at hI
    simpa [ENNReal.toReal_ofReal (h₇ sₜ u _)] using hI
  have hn : ∀ aₜ, ∫ y, ‖M.π θ sₜ aₜ • (p sₜ aₜ y • fderiv ℝ (fun θ => M.V0 R θ γ y) θ)‖ ∂ReferenceMeasure.measure ≤
      M.π θ sₜ aₜ * C := fun aₜ => by
    have e : ∫ y, ‖M.π θ sₜ aₜ • (p sₜ aₜ y • fderiv ℝ (fun θ => M.V0 R θ γ y) θ)‖ ∂ReferenceMeasure.measure =
        ∫ y, M.π θ sₜ aₜ * ‖fderiv ℝ (fun θ => M.V0 R θ γ y) θ‖ ∂(M.trans (sₜ, aₜ)) := by
      rw [h₈, integral_withDensity_eq_integral_toReal_smul (hp aₜ).ennreal_ofReal
        (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
      congr 1
      funext y
      have hπnn : 0 ≤ M.π θ sₜ aₜ := hStoch.nonneg θ sₜ aₜ
      rw [ENNReal.toReal_ofReal (h₇ sₜ aₜ y), norm_smul, norm_smul,
        Real.norm_of_nonneg hπnn, Real.norm_of_nonneg (h₇ sₜ aₜ y), smul_eq_mul]
      ring
    have h := norm_integral_le_of_norm_le_const (μ := M.trans (sₜ, aₜ)) (C := C)
      (f := fun y => ‖fderiv ℝ (fun θ => M.V0 R θ γ y) θ‖) (Filter.Eventually.of_forall fun y => by
        rw [norm_norm]
        exact hCb y)
    rw [e, integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans (by simpa using h)) (hStoch.nonneg θ sₜ aₜ)
  have hFm : StronglyMeasurable (fun z : 𝒜 × 𝒮 => M.π θ sₜ z.1 • (p sₜ z.1 z.2 • fderiv ℝ (fun θ => M.V0 R θ γ z.2) θ)) :=
    (hπm.comp measurable_fst).stronglyMeasurable.smul ((h₆ sₜ).stronglyMeasurable.smul (hgm.comp_measurable measurable_snd))
  have hInt : Integrable (Function.uncurry fun aₜ y => M.π θ sₜ aₜ • (p sₜ aₜ y • fderiv ℝ (fun θ => M.V0 R θ γ y) θ))
      (ReferenceMeasure.measure.prod ReferenceMeasure.measure) :=
    (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall fun aₜ => (hi aₜ).smul (M.π θ sₜ aₜ),
      (hπ.mul_const C).mono' (hFm.norm.integral_prod_right' (ν := ReferenceMeasure.measure)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun aₜ => by
          rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
          exact hn aₜ)⟩
  have hsum : ∫ aₜ, (M.π θ sₜ aₜ • ∫ y, fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂(M.trans (sₜ, aₜ))) ∂ReferenceMeasure.measure =
      ∫ y, (M.P1kd θ p sₜ y • fderiv ℝ (fun θ => M.V0 R θ γ y) θ) ∂ReferenceMeasure.measure := calc
    _ = ∫ aₜ, ∫ y, M.π θ sₜ aₜ • (p sₜ aₜ y • fderiv ℝ (fun θ => M.V0 R θ γ y) θ) ∂ReferenceMeasure.measure ∂ReferenceMeasure.measure := by
      congr 1
      funext u
      rw [hd u, integral_smul]
    _ = ∫ y, ∫ aₜ, M.π θ sₜ aₜ • (p sₜ aₜ y • fderiv ℝ (fun θ => M.V0 R θ γ y) θ) ∂ReferenceMeasure.measure ∂ReferenceMeasure.measure :=
      integral_integral_swap hInt
    _ = _ := by
      congr 1
      funext y
      simp only [smul_smul, integral_smul_const, Model.P1kd]
  have hint₁ : (InnerProductSpace.toDual ℝ Θ).symm (∫ aₜ, (M.rkd R sₜ aₜ + γ * ∫ y, M.V0 R θ γ y ∂(M.trans (sₜ, aₜ))) • fderiv ℝ (fun θ => M.π θ sₜ aₜ) θ ∂ReferenceMeasure.measure) =
      ∫ aₜ, (InnerProductSpace.toDual ℝ Θ).symm ((M.rkd R sₜ aₜ + γ * ∫ y, M.V0 R θ γ y ∂(M.trans (sₜ, aₜ))) • fderiv ℝ (fun θ => M.π θ sₜ aₜ) θ) ∂ReferenceMeasure.measure := by
    have h := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := ReferenceMeasure.measure) (fun aₜ => (M.rkd R sₜ aₜ + γ * ∫ y, M.V0 R θ γ y ∂(M.trans (sₜ, aₜ))) • fderiv ℝ (fun θ => M.π θ sₜ aₜ) θ)
    simpa using h.symm
  have hint₂ : (InnerProductSpace.toDual ℝ Θ).symm (∫ y, M.P1kd θ p sₜ y • fderiv ℝ (fun θ => M.V0 R θ γ y) θ ∂ReferenceMeasure.measure) =
      ∫ y, (InnerProductSpace.toDual ℝ Θ).symm (M.P1kd θ p sₜ y • fderiv ℝ (fun θ => M.V0 R θ γ y) θ) ∂ReferenceMeasure.measure := by
    have h := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := ReferenceMeasure.measure) (fun y => M.P1kd θ p sₜ y • fderiv ℝ (fun θ => M.V0 R θ γ y) θ)
    simpa using h.symm
  simp only [gradient]
  rw [hF, hsum, map_add, map_smul, hint₁, hint₂]
  simp [map_smul]


-- created on 2026-10-07
-- updated on 2026-11-18
