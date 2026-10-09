import Lemma.Random.GradVkd.eq.AddIntegral_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico
import sympy.concrete.summations
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Dirac
open MeasureTheory PolicyGradient Random


/--
Policy-gradient recursion with a discrete (finite) state space and a continuous action space:
∇V(s[t] = s.bvar[t]) = ∫ u, Q(s.bvar[t], u) • ∇π(u | s.bvar[t]) du + γ • ∑ s.bvar[t+1], Pr(s[t+1] = s.bvar[t+1] | s[t] = s.bvar[t]) • ∇V(s[t+1] = s.bvar[t+1]),
the fourth case next to the discrete/discrete
`Random.Grad.eq.Add_SMul_Sum_SMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.All_Eq_Expect.All_Eq_Expect.EqMeasureCount.EqMeasureCount.In_Ico`,
the continuous-state/discrete-action
`Random.GradVk.eq.Add_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Differentiable_Prob.In_Ico`
and the continuous/continuous
`Random.GradVkd.eq.AddIntegral_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico`
versions. It is the corollary of the latter for the counting measure on the finite state space `S` (as in the
discrete version, whose state sums are integrals against `Measure.count`): the next-state integral becomes the finite sum
`∑ s.bvar[t+1]`, and the transition density becomes the transition probability mass function `p x u y = T({y} | x, u)`
(h₆), so `P1kd θ p x y = ∫ u, π_θ(u | x) * T({y} | x, u) du = Pr(s[t+1] = y | s[t] = x)`.
On a finite state space with measurable singletons every function of the state is measurable, so the hypotheses of the
continuous-state version simplify: joint measurability of the policy becomes measurability in the action (h₅), and the
nonnegativity, measurability and density hypotheses on `p` all follow from h₆.
h₁: θ ↦ π_θ(u | x) is differentiable; h₂, h₃, h₄: its gradient is dominated by `g x u`, where `g x` is integrable over
the actions uniformly in the state. `V = Vkd`, `Q = Qkd` are the closed-form values of
`sympy.stats.policy_trajectory.continuous_action`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A]
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
  (h₅ : ∀ θ x, Measurable (M.pol.prob θ x))
  (h₆ : ∀ x u y, (M.env.trans (x, u)).real {y} = p x u y) :
-- imply
  ∇[θ] M.Vkd θ γ («s.bvar» t) =
    ∫ u, M.Qkd θ γ («s.bvar» t) u • ∇[θ] M.pol.prob θ («s.bvar» t) u ∂ReferenceMeasure.measure +
      γ • (∑ «s.bvar» (t + 1), M.P1kd θ p («s.bvar» t) («s.bvar» (t + 1)) • ∇[θ] M.Vkd θ γ («s.bvar» (t + 1))) := by
-- proof
  let : ReferenceMeasure S := ReferenceMeasure.of Measure.count
  have := M.env.trans_markov
  have hT : ∀ x u, M.env.trans (x, u) =
      (ReferenceMeasure.measure : Measure S).withDensity (fun y => ENNReal.ofReal (p x u y)) := by
    intro x u
    show M.env.trans (x, u) = Measure.count.withDensity fun y => ENNReal.ofReal (p x u y)
    rw [Measure.ext_iff_singleton]
    intro y
    rw [withDensity_apply _ (measurableSet_singleton y), lintegral_singleton, Measure.count_singleton, mul_one, ← h₆,
      ofReal_measureReal]
  rw [GradVkd.eq.AddIntegral_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico
    (M := M) (θ := θ) (t := t) («s.bvar» := «s.bvar») h₀ h₁ h₂ h₃ h₄
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
