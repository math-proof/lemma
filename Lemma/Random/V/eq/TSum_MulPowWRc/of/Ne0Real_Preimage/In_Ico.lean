import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral.eq.MulRealPreimageSIntegral_MulEqS
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Integral_MulEqSR_Add.eq.MulRealPreimageSWRc
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
On a reachable state (`Pr(s[t] = x) ≠ 0`): `V θ γ t x = ∑' k, γ ^ k * W θ rc k x`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (hγ : γ ∈ Set.Ico 0 1)
  (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  M.V θ γ t x = ∑' k, γ ^ k * M.W θ M.rc k x := by
-- proof
  rw [V_eq_integral, Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) hγ θ]
  congr 1; funext k
  rw [Integral.eq.MulRealPreimageSIntegral_MulEqS, Integral_MulEqSR_Add.eq.MulRealPreimageSWRc, inv_mul_cancel_left₀ hP]


-- created on 2026-10-07
