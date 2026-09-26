import sympy.stats.policy_trajectory.markov
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
`γ ** Stack[k](k) @ 𝔼[r[t:] | s[t] = x] = 𝔼_{a[t] ∼ π}[Q(s[t] = x, a[t]) | s[t] = x]`:
the discounted state value is the policy average of the action values `Q` given by `h₁` (the sympy `Q_def`).
The discount factor is taken in `[0, 1)` (for `γ = 1` the Lean `tsum` of a divergent series is `0`
and the identity fails).
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {Q : S → A → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ x u, Q x u = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}])
  (x : S) :
-- imply
  ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}] =
    ∫ ω, Q x (a t ω) ∂(M.traj θ)[|s t ⁻¹' {x}] := by
-- proof
  classical
  have h₂ : Q = M.Q θ γ t := funext fun x => funext fun u => h₁ x u
  subst h₂
  show M.V θ γ t x = _
  by_cases hP : (M.traj θ).real (s t ⁻¹' {x}) = 0
  · have h₃ := cond_eq_zero_of_meas_eq_zero (meas_zero_of_real M θ hP)
    simp [Model.V, h₃]
  · rw [V_eq M θ γ t x hP, cond_s]
    have h₃ : ∀ ω, (if s t ω = x then (1:ℝ) else 0) * M.Q θ γ t x (a t ω) =
        ∑ u, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * M.Q θ γ t x u := by
      intro ω
      rw [Finset.sum_eq_single (a t ω) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      by_cases h : s t ω = x <;> simp [h]
    simp_rw [h₃]
    rw [integral_finsetSum _ (fun u _ => integrable_ind_sa M θ t x u _)]
    simp_rw [integral_mul_const, P_xu]
    rw [Finset.mul_sum]
    have h₄ : ∀ u, ((M.traj θ).real (s t ⁻¹' {x}))⁻¹ *
        ((M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * M.Q θ γ t x u) =
        M.pol.prob θ x u * ((∫ ρ, M.rc (x, u, ρ) ∂(M.env.reward (x, u))) +
          γ * ∑ y, M.T x u y * ∑' k, γ ^ k * M.W θ M.rc k y) := by
      intro u
      rw [mul_assoc, inv_mul_cancel_left₀ hP]
      by_cases hu : M.pol.prob θ x u = 0
      · simp [hu]
      · rw [Q_eq M θ h₀ t x u (mul_ne_zero hP hu)]
    simp_rw [h₄]
    rw [v_closed M θ h₀ x, W_zero M θ (rc_sm M) (rc_bdd M) x, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => by ring)


-- created on 2026-09-26
