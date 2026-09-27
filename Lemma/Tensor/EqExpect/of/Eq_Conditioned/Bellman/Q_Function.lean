import sympy.stats.policy_trajectory.markov
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Bellman equation for the action value of the trajectory model:
`γ ** Stack[k](k) @ 𝔼[r[t:] | s[t] = x, a[t] = u]
  = 𝔼[γ * (γ ** Stack[k](k) @ 𝔼[r[t+1:] | s[t+1]]) + r[t] | s[t] = x, a[t] = u]`.
`_h₀` is the sympy reward hypothesis `Equal(r[t] | s[:t] & a[:t], r[t])`; it is kept as a named hypothesis
but is not needed, since the environment of `PolicyGradient.Model` is a (Markov) MDP.
Both sides are `0` when `s[t] = x ∧ a[t] = u` has probability `0`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
-- given
  (_h₀ : IndepFun (r t) (fun ω (i : Fin t) => (s i ω, a i ω)) (M.traj θ))
  (h₁ : γ ∈ Set.Ico 0 1)
  (x : S)
  (u : A) :
-- imply
  ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] =
    ∫ ω, γ * (∑' k, γ ^ k * ∫ ω', r (t + 1 + k) ω' ∂(M.traj θ)[|s (t + 1) ⁻¹' {s (t + 1) ω}]) + r t ω
      ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] := by
-- proof
  classical
  show M.Q θ γ t x u = ∫ ω, γ * M.V θ γ (t + 1) (s (t + 1) ω) + r t ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}]
  by_cases hP : (M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u = 0
  · rw [← real_sa] at hP
    have h₂ := cond_eq_zero_of_meas_eq_zero (meas_zero_of_real M θ hP)
    simp [Model.Q, h₂]
  · have hP₀ : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0 := left_ne_zero_of_mul hP
    have hu : M.pol.prob θ x u ≠ 0 := right_ne_zero_of_mul hP
    rw [cond_sa]
    have h₂ : ∀ ω : ℕ → Step S A, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
        (γ * M.V θ γ (t + 1) (s (t + 1) ω) + r t ω) =
        γ * ((if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * M.V θ γ (t + 1) (s (t + 1) ω)) +
          (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r t ω := fun ω => by ring
    simp_rw [h₂]
    rw [integral_add ((integrable_ind_h M θ (fun ω => ((s t ω, a t ω), s (t + 1) ω))
        (((s_meas t).prodMk (a_meas t)).prodMk (s_meas (t + 1)))
        (fun p => (if p.1.1 = x ∧ p.1.2 = u then (1:ℝ) else 0) * M.V θ γ (t + 1) p.2)).const_mul γ)
      (integrable_ind_r M θ (fun ω => (s t ω, a t ω)) ((s_meas t).prodMk (a_meas t))
        (fun p => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0) t),
      integral_const_mul, E_xu_h, E_xu_r0, alg1 hP, Q_eq M θ h₁ t x u hP]
    congr 2
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have h₃ := V_succ_eq M θ γ t x u hP₀ y
    exact (mul_left_cancel₀ hu h₃).symm


-- created on 2026-09-26
