import sympy.stats.rv
import sympy.stats.policy_trajectory.continuous_action
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Prod
import Lemma.Random.Fderiv.eq.AddIntegral_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob
import Lemma.Random.Measurable_Vkd.of.All_Measurable_Prob
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
open MeasureTheory PolicyGradient Random Real


/--
Policy-gradient recursion with a continuous state space and a continuous action space:
∇V(s[t] = s.bvar[t]) = ∫ u, Q(s.bvar[t], u) • ∇π(u | s.bvar[t]) du + γ • ∫ y, Pr(s[t+1] = y | s[t] = s.bvar[t]) • ∇V(s[t+1] = y) dy,
the gradient of the Bellman equations of extract_QVA; both the action sum and the next-state sum of the discrete version
`Random.Grad.eq.Add_SMul_Sum_SMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.All_Eq_Expect.All_Eq_Expect.EqMeasureCount.EqMeasureCount.In_Ico`
become integrals against the reference measures of `A` and `S` (e.g. Lebesgue measures on `ℝ^m`, `ℝ^b`).
Continuous-action counterpart of
`Random.GradVk.eq.Add_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Differentiable_Prob.In_Ico`.
The policy `π_θ(u | x)` is a probability density w.r.t. the reference measure of `A` (`DensityPolicy`); `V = Vkd`, `Q = Qkd`
are the regular (kernel) conditional expectations of the discounted return `γ ** Stack[k](k) @ r[t:]` given `s[t] = x`
(resp. `s[t] = x, a[t] = u`), see `sympy.stats.policy_trajectory.continuous_action`;
`Pr(s[t+1] = y | s[t] = x) = P1kd θ p x y = ∫ u, π_θ(u | x) * p x u y du`.
h₁: θ ↦ π_θ(u | x) is differentiable; h₂, h₃, h₄: its gradient is dominated by `g x u`, where `g x` is integrable over
the actions uniformly in the state (this replaces `sup ‖∇π‖ < ∞` of the finite-action version, where `∑ u` is
integration against the counting measure); h₅: (x, u) ↦ π_θ(u | x) is jointly measurable; h₆, h₇, h₈: `p x u` is a
nonnegative density of the transition `T(· | x, u)` w.r.t. the reference measure of `S`, jointly measurable in the
action and the next state (for Fubini). `Θ` is finite-dimensional (the weights `π` have shape `(D,)`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [ReferenceMeasure S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {«s.bvar» : ℕ → S}
  {g : S → A → ℝ}
  {p : S → A → S → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₂ : ∀ θ x u, ‖∇[θ] M.pol.prob θ x u‖ ≤ g x u)
  (h₃ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (h₄ : sup[x] ∫ u, g x u ∂ReferenceMeasure.measure < ∞)
  (h₅ : ∀ θ, Measurable (fun z : S × A => M.pol.prob θ z.1 z.2))
  (h₆ : ∀ x, Measurable (fun z : A × S => p x z.1 z.2))
  (h₇ : ∀ x u y, p x u y ≥ 0)
  (h₈ : ∀ x u, M.env.trans (x, u) = (ReferenceMeasure.measure : Measure S).withDensity (fun y => ENNReal.ofReal (p x u y))) :
-- imply
  ∇[θ] M.Vkd θ γ («s.bvar» t) =
    ∫ u, M.Qkd θ γ («s.bvar» t) u • ∇[θ] M.pol.prob θ («s.bvar» t) u ∂ReferenceMeasure.measure +
      γ • ∫ y, M.P1kd θ p («s.bvar» t) y • ∇[θ] M.Vkd θ γ y ∂ReferenceMeasure.measure := by
-- proof
  set x := «s.bvar» t
  have := M.env.trans_markov
  have hF := Fderiv.eq.AddIntegral_SMulSMul.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₁ h₂ h₃ h₄ h₀ h₅ x θ
  obtain ⟨C, hC⟩ := GtInftySup.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₁ h₂ h₃ h₄ h₀ h₅
  have hCb : ∀ y, ‖fderiv ℝ (fun θ => M.Vkd θ γ y) θ‖ ≤ C := fun y => by
    have h := hC ⟨(θ, y), rfl⟩
    simpa [gradient, LinearIsometryEquiv.norm_map] using h
  have hgm : StronglyMeasurable (fun y => fderiv ℝ (fun θ => M.Vkd θ γ y) θ) :=
    StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
      (fun θ' => Measurable_Vkd.of.All_Measurable_Prob (M := M) h₅ θ' γ)
      (fun y => (HasFDerivAt.of.All_Measurable_Prob.In_Ico.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob (M := M) h₁ h₂ h₃ h₄ h₀ h₅ y θ).differentiableAt)
  have hπ : Integrable (M.pol.prob θ x) ReferenceMeasure.measure :=
    Integrable.of_integral_ne_zero (by rw [M.pol.integral_eq_one θ x]; exact one_ne_zero)
  have hπm : Measurable (M.pol.prob θ x) := (h₅ θ).comp measurable_prodMk_left
  have hp : ∀ u, Measurable (p x u) := fun u => (h₆ x).comp measurable_prodMk_left
  have hd : ∀ u, ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u)) =
      ∫ y, p x u y • fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂ReferenceMeasure.measure := fun u => by
    rw [h₈, integral_withDensity_eq_integral_toReal_smul (hp u).ennreal_ofReal
      (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal (h₇ x u _)]
  have hi : ∀ u, Integrable (fun y => p x u y • fderiv ℝ (fun θ => M.Vkd θ γ y) θ) ReferenceMeasure.measure := fun u => by
    have hI : Integrable (fun y => fderiv ℝ (fun θ => M.Vkd θ γ y) θ) (M.env.trans (x, u)) :=
      Integrable.of_bound hgm.aestronglyMeasurable C (Filter.Eventually.of_forall hCb)
    rw [h₈, integrable_withDensity_iff_integrable_smul' (hp u).ennreal_ofReal
      (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)] at hI
    simpa [ENNReal.toReal_ofReal (h₇ x u _)] using hI
  have hn : ∀ u, ∫ y, ‖M.pol.prob θ x u • (p x u y • fderiv ℝ (fun θ => M.Vkd θ γ y) θ)‖ ∂ReferenceMeasure.measure ≤
      M.pol.prob θ x u * C := fun u => by
    have e : ∫ y, ‖M.pol.prob θ x u • (p x u y • fderiv ℝ (fun θ => M.Vkd θ γ y) θ)‖ ∂ReferenceMeasure.measure =
        ∫ y, M.pol.prob θ x u * ‖fderiv ℝ (fun θ => M.Vkd θ γ y) θ‖ ∂(M.env.trans (x, u)) := by
      rw [h₈, integral_withDensity_eq_integral_toReal_smul (hp u).ennreal_ofReal
        (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
      congr 1
      funext y
      rw [ENNReal.toReal_ofReal (h₇ x u y), norm_smul, norm_smul, Real.norm_of_nonneg (M.pol.nonneg θ x u),
        Real.norm_of_nonneg (h₇ x u y), smul_eq_mul]
      ring
    have h := norm_integral_le_of_norm_le_const (μ := M.env.trans (x, u)) (C := C)
      (f := fun y => ‖fderiv ℝ (fun θ => M.Vkd θ γ y) θ‖) (Filter.Eventually.of_forall fun y => by
        rw [norm_norm]
        exact hCb y)
    rw [e, integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((Real.le_norm_self _).trans (by simpa using h)) (M.pol.nonneg θ x u)
  have hFm : StronglyMeasurable (fun z : A × S => M.pol.prob θ x z.1 • (p x z.1 z.2 • fderiv ℝ (fun θ => M.Vkd θ γ z.2) θ)) :=
    (hπm.comp measurable_fst).stronglyMeasurable.smul ((h₆ x).stronglyMeasurable.smul (hgm.comp_measurable measurable_snd))
  have hInt : Integrable (Function.uncurry fun u y => M.pol.prob θ x u • (p x u y • fderiv ℝ (fun θ => M.Vkd θ γ y) θ))
      ((ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S)) :=
    (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall fun u => (hi u).smul (M.pol.prob θ x u),
      (hπ.mul_const C).mono' (hFm.norm.integral_prod_right' (ν := (ReferenceMeasure.measure : Measure S))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => by
          rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
          exact hn u)⟩
  have hsum : ∫ u, M.pol.prob θ x u • ∫ y, fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂(M.env.trans (x, u)) ∂ReferenceMeasure.measure =
      ∫ y, M.P1kd θ p x y • fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂ReferenceMeasure.measure := calc
    _ = ∫ u, ∫ y, M.pol.prob θ x u • (p x u y • fderiv ℝ (fun θ => M.Vkd θ γ y) θ) ∂ReferenceMeasure.measure ∂ReferenceMeasure.measure := by
      congr 1
      funext u
      rw [hd u, integral_smul]
    _ = ∫ y, ∫ u, M.pol.prob θ x u • (p x u y • fderiv ℝ (fun θ => M.Vkd θ γ y) θ) ∂ReferenceMeasure.measure ∂ReferenceMeasure.measure :=
      integral_integral_swap hInt
    _ = _ := by
      congr 1
      funext y
      simp only [smul_smul, integral_smul_const, DensityModel.P1kd]
  have hint₁ : (InnerProductSpace.toDual ℝ Θ).symm (∫ u, M.Qkd θ γ x u • fderiv ℝ (fun θ => M.pol.prob θ x u) θ ∂ReferenceMeasure.measure) =
      ∫ u, (InnerProductSpace.toDual ℝ Θ).symm (M.Qkd θ γ x u • fderiv ℝ (fun θ => M.pol.prob θ x u) θ) ∂ReferenceMeasure.measure := by
    have h := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := (ReferenceMeasure.measure : Measure A)) (fun u => M.Qkd θ γ x u • fderiv ℝ (fun θ => M.pol.prob θ x u) θ)
    simpa using h.symm
  have hint₂ : (InnerProductSpace.toDual ℝ Θ).symm (∫ y, M.P1kd θ p x y • fderiv ℝ (fun θ => M.Vkd θ γ y) θ ∂ReferenceMeasure.measure) =
      ∫ y, (InnerProductSpace.toDual ℝ Θ).symm (M.P1kd θ p x y • fderiv ℝ (fun θ => M.Vkd θ γ y) θ) ∂ReferenceMeasure.measure := by
    have h := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv.integral_comp_comm
      (μ := (ReferenceMeasure.measure : Measure S)) (fun y => M.P1kd θ p x y • fderiv ℝ (fun θ => M.Vkd θ γ y) θ)
    simpa using h.symm
  simp only [gradient]
  rw [hF, hsum, map_add, map_smul, hint₁, hint₂]
  simp [map_smul]


-- created on 2026-10-07
