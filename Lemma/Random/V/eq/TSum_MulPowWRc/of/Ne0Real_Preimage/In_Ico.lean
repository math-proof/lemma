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
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  M.V r s θ γ t x = ∑' k, γ ^ k * M.W θ M.rc k x := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  rw [M.V_eq_integral r s]
  show ∫ ω, G r γ t ω ∂(M θ)[|s t ⁻¹' {x}] = _
  rw [Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) hγ h₁ θ]
  congr 1; funext k
  rw [Integral.eq.MulRealPreimageSIntegral_MulEqS h₁, Integral_MulEqSR_Add.eq.MulRealPreimageSWRc h₁, inv_mul_cancel_left₀ hP]


-- created on 2026-10-07
