import sympy.stats.policy_trajectory.markov
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Bellman equation for the state value of the trajectory model:
`γ ** Stack[k](k) @ 𝔼[r[t:] | s[t] = x] = 𝔼[γ * (γ ** Stack[k](k) @ 𝔼[r[t+1:] | s[t+1]]) + r[t] | s[t] = x]`.
No history-independence hypothesis on the rewards is needed, since the environment of
`PolicyGradient.Model` is a (Markov) MDP.
Both sides are `0` when `s[t] = x` has probability `0`.
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
  (h₁ : γ ∈ Set.Ico 0 1)
  (x : S) :
-- imply
  ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}] =
    ∫ ω, γ * (∫ ω', ∑' k, γ ^ k * r (t + 1 + k) ω' ∂(M.traj θ)[|s (t + 1) ⁻¹' {s (t + 1) ω}]) + r t ω
      ∂(M.traj θ)[|s t ⁻¹' {x}] := by
-- proof
  classical
  have hVi : ∀ t x, ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}] = M.V θ γ t x :=
    fun t x => (M.V_eq_integral θ γ t x).symm
  simp only [hVi]
  by_cases hP : (M.traj θ).real (s t ⁻¹' {x}) = 0
  · have h₂ := cond_eq_zero_of_meas_eq_zero (meas_zero_of_real M θ hP)
    simp [M.V_eq_integral, h₂]
  · rw [cond_s]
    have h₂ : ∀ ω : ℕ → S × A × ℝ, (if s t ω = x then (1:ℝ) else 0) *
        (γ * M.V θ γ (t + 1) (s (t + 1) ω) + r t ω) =
        γ * ((if s t ω = x then (1:ℝ) else 0) * M.V θ γ (t + 1) (s (t + 1) ω)) +
          (if s t ω = x then (1:ℝ) else 0) * r t ω := fun ω => by ring
    simp_rw [h₂]
    rw [integral_add ((integrable_ind_h M θ (fun ω => (s t ω, s (t + 1) ω))
        ((s_meas t).prodMk (s_meas (t + 1)))
        (fun p => (if p.1 = x then (1:ℝ) else 0) * M.V θ γ (t + 1) p.2)).const_mul γ)
      (integrable_ind_r M θ (s t) (s_meas t) (fun y => if y = x then (1:ℝ) else 0) t),
      integral_const_mul]
    have h₃ := E_s_r M θ t 0 x
    simp only [add_zero] at h₃
    have h₄ := E_s_h M θ t x (M.V θ γ (t + 1))
    rw [h₃, h₄, V_eq M θ h₁ t x hP, v_closed M θ h₁ x, alg1 hP]
    congr 2
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => (V_succ_eq M θ h₁ t x u hP y).symm)


-- created on 2026-09-26
