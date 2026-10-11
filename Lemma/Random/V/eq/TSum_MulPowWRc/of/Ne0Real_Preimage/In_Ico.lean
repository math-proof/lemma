import sympy.stats.policy_trajectory
import sympy.stats.cond_expectation
import Lemma.Random.Integral.eq.MulRealPreimageSIntegral_MulEqS
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Integral_MulEqSR_Add.eq.MulRealPreimageSWRc
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
On a reachable state (`Pr(s[t] = x) ≠ 0`): `V θ γ t x = ∑' k, γ ^ k * W θ rc k x`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  let V (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x);
  V θ t x = ∑' k, γ ^ k * M.W θ M.rc k x := by
-- proof
  set G := (γ ^ (id : ℕ → ℕ)) @ r[t:]
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  simp only [Expectation.asRV_process]
  rw [Expectation.condEvent_eq_integral hpR.aemeasurable hfG]
  show ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ)[|s t ⁻¹' {x}] = _
  rw [Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ h₁ θ]
  congr 1; funext k
  rw [Integral.eq.MulRealPreimageSIntegral_MulEqS h₁, Integral_MulEqSR_Add.eq.MulRealPreimageSWRc h₁, inv_mul_cancel_left₀ hP]


-- created on 2026-10-07
-- updated on 2026-10-10
