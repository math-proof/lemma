import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.RealInterPreimageS_PreimageA.eq.MulRealPreimageSProb
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


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
  (M θ).real (state t ⁻¹' {x} ∩ action t ⁻¹' {u}) = (M θ).real (state t ⁻¹' {x}) * M.Pr θ x u := by
-- proof
  classical
  exact RealInterPreimageS_PreimageA.eq.MulRealPreimageSProb (M := M) θ t x u


-- created on 2026-09-26
