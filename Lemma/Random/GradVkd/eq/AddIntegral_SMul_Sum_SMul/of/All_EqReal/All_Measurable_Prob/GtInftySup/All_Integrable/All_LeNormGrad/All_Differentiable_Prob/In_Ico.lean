import Lemma.Random.GradVkd.eq.AddIntegral_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico
import Syntax.Algebra.BigOperators.Summations
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
open MeasureTheory PolicyGradient Random


/--
Policy-gradient recursion with a discrete (finite) state space and a continuous action space:
∇V(s[t] = s.bvar[t]) = ∫ u, (rkd + γ * ∫ V0)(s.bvar[t], u) • ∇π(u | s.bvar[t]) du + γ • ∑ s.bvar[t+1], ℙ(s[t+1] = s.bvar[t+1] | s[t] = s.bvar[t]) • ∇V(s[t+1] = s.bvar[t+1]),
the finite-state counterpart of the continuous/continuous
`Random.GradVkd.eq.AddIntegral_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico`
versions. It is the corollary of the latter for the counting measure on the finite state space `𝒮` (as in the
discrete version, whose state sums are integrals against `Measure.count`): the next-state integral becomes the finite sum
`∑ s.bvar[t+1]`, and the transition density becomes the transition probability mass function `p x u y = T({y} | x, u)`
(h₆), so `P1kd θ p x y = ∫ u, π_θ(u | x) * T({y} | x, u) du = ℙ(s[t+1] = y | s[t] = x)`.
On a finite state space with measurable singletons every function of the state is measurable, so the hypotheses of the
continuous-state version simplify: joint measurability of the policy becomes measurability in the action (h₅), and the
nonnegativity, measurability and density hypotheses on `p` all follow from h₆.
h₁: θ ↦ π_θ(u | x) is differentiable; h₂, h₃, h₄: its gradient is dominated by `g x u`, where `g x` is integrable over
the actions uniformly in the state. `V = V0` is the discounted `Wkd` series, and the action-value is the closed form
`rkd + γ * ∫ V0 ∂T`, so no reachability hypothesis is needed.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [μ : ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {«\sf{s}» : ℕ → 𝒮}
  {g : 𝒮 → 𝒜 → ℝ}
  {p : 𝒮 → 𝒜 → 𝒮 → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₂ : ∀ θ x u, ‖∇[θ] M.policy.prob θ x u‖ ≤ g x u)
  (h₃ : ∀ x, Integrable (g x) μ.measure)
  (h₄ : sup[x] ∫ u, g x u ∂μ.measure < ∞)
  (h₅ : ∀ θ x, Measurable (M.policy.prob θ x))
  (h₆ : ∀ x u y, (M.env.trans (x, u)).real {y} = p x u y) :
-- imply
  ∇[θ] M.V0 θ γ («\sf{s}» t) =
    ∫ u, ((M.rkd («\sf{s}» t) u + γ * ∫ y, M.V0 θ γ y ∂(M.env.trans («\sf{s}» t, u))) •
        ∇[θ] M.policy.prob θ («\sf{s}» t) u) ∂μ.measure +
      γ • (∑ «\sf{s}» (t + 1), M.P1kd θ p («\sf{s}» t) («\sf{s}» (t + 1)) • ∇[θ] M.V0 θ γ («\sf{s}» (t + 1))) := by
-- proof
  let : ReferenceMeasure 𝒮 := ReferenceMeasure.of Measure.count
  have := M.env.trans_markov
  have hT : ∀ x u, M.env.trans (x, u) =
      (ReferenceMeasure.measure : Measure 𝒮).withDensity (fun y => ENNReal.ofReal (p x u y)) := by
    intro x u
    show M.env.trans (x, u) = Measure.count.withDensity fun y => ENNReal.ofReal (p x u y)
    rw [Measure.ext_iff_singleton]
    intro y
    rw [withDensity_apply _ (measurableSet_singleton y), lintegral_singleton, Measure.count_singleton, mul_one, ← h₆,
      ofReal_measureReal]
  rw [GradVkd.eq.AddIntegral_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico
    (M := M) (θ := θ) (t := t) («\sf{s}» := «\sf{s}») h₀ h₁ h₂ h₃ h₄
    (fun θ => measurable_from_prod_countable_right fun x => h₅ θ x)
    (fun x => measurable_from_prod_countable_left fun y => by
      simp_rw [← h₆]
      apply ((M.env.trans.measurable_coe (measurableSet_singleton y)).comp measurable_prodMk_left).ennreal_toReal)
    (fun x u y => by
      rw [← h₆]
      apply measureReal_nonneg) hT]
  congr 2
  apply integral_count


-- created on 2026-10-07
-- updated on 2026-11-14
