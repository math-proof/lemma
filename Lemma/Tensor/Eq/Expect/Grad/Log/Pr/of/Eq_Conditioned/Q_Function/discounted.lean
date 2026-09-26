import sympy.stats.policy_trajectory.gradient
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
`𝔼[∇ log π(a[t] | s[t]) * (γ ** Stack[k](k) @ r[t:])] =
  𝔼[∇ log π(a[t] | s[t]) * (γ ** Stack[k](k) @ 𝔼[r[t:] | s[t], a[t]])]`
(law of iterated expectation on `(s[t], a[t])`); `h₀` is the sympy reward hypothesis.
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
-- given
  (_h₀ : IndepFun (r t) (fun ω (i : Fin t) => (s i ω, a i ω)) (M.traj θ))
  (h₁ : γ ∈ Set.Ico 0 1) :
-- imply
  ∫ ω, (∑' k, γ ^ k * r (t + k) ω) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) =
    ∫ ω, (∑' k, γ ^ k * ∫ ω', r (t + k) ω' ∂(M.traj θ)[|s t ⁻¹' {s t ω} ∩ a t ⁻¹' {a t ω}]) •
      fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) := by
-- proof
  classical
  exact E_G_smul M θ h₁ t (fun x u => fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' x u)) θ)


-- created on 2026-09-26
