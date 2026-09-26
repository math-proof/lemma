import sympy.stats.policy_trajectory.markov
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Joint law of state and action in the trajectory model:
`Pr(s[t] = x, a[t] = u) = Pr(s[t] = x) * Pr[a:π](a[t] = u | s[t] = x)`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {t : ℕ}
-- given
  (x : S)
  (u : A) :
-- imply
  (M.traj θ).real (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) = (M.traj θ).real (s t ⁻¹' {x}) * M.Pr θ x u := by
-- proof
  classical
  exact real_sa M θ t x u


-- created on 2026-09-26
