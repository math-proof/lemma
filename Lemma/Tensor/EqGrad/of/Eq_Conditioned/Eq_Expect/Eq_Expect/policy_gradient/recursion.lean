import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Policy-gradient recursion: on a reachable state `x` (`h₆ : Pr(s[t] = x) ≠ 0`),
`∇V(s[t] = x) = ∑ u, Q(x, u) • ∇π(u | x) + γ • ∑ y, Pr(s[t+1] = y | s[t] = x) • ∇V(s[t+1] = y)`,
the gradient of the Bellman equations of `extract_QVA`. `Q`, `V` are the action and state values
(`h₁`, `h₂`, the sympy `Q_def`, `V_def`) as functions of the weights `θ`; `h₀` is the sympy reward
hypothesis; `h₄`, `h₅`: `θ ↦ π_θ(u | x)` is differentiable with a bounded gradient.
Cond.Prob.of.Cond.weighted is definitional here: every probability is taken under `M.traj θ`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {x : S}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
-- given
  (_h₀ : IndepFun (r t) (fun ω (i : Fin t) => (s i ω, a i ω)) (M.traj θ))
  (h₁ : ∀ θ t x u, Q θ t x u = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}])
  (h₂ : ∀ θ t x, V θ t x = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}])
  (h₃ : γ ∈ Set.Ico 0 1)
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₅ : BddAbove (Set.range fun p : Θ × S × A => ‖fderiv ℝ (fun θ => M.pol.prob θ p.2.1 p.2.2) p.1‖))
  (h₆ : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  fderiv ℝ (fun θ => V θ t x) θ =
    ∑ u, Q θ t x u • fderiv ℝ (fun θ => M.pol.prob θ x u) θ +
      γ • ∑ y, ((M.traj θ)[|s t ⁻¹' {x}]).real (s (t + 1) ⁻¹' {y}) • fderiv ℝ (fun θ => V θ (t + 1) y) θ := by
-- proof
  have hQ : Q = fun θ => M.Q θ γ :=
    funext fun θ => funext fun t => funext fun x => funext fun u => h₁ θ t x u
  have hV : V = fun θ => M.V θ γ := funext fun θ => funext fun t => funext fun x => h₂ θ t x
  subst hQ hV
  obtain ⟨C, hC⟩ := id h₅
  have h₇ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  classical
  beta_reduce
  rw [grad_V_rec M h₄ h₇ h₃ t x θ h₆]
  simp_rw [cond_P1 M θ t x _ h₆]


-- created on 2026-09-26
