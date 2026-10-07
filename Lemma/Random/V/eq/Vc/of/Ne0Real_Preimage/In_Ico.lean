import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Random.V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
On a reachable state (`Pr(s[t] = x) ≠ 0`), the state value equals its time-free closed form: `V θ γ t x = Vc θ γ x`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (t : ℕ)
  (x : S)
  (h₁ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  M.V θ γ t x = M.Vc θ γ x := by
-- proof
  exact V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) θ t x h₀ h₁


-- created on 2026-10-06
