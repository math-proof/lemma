import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Eq_0.of.EqReal_0
import Lemma.Random.Integrable.of.Measurable
import Lemma.Random.Integrable_Mul_R.of.Measurable
import Lemma.Random.Integral.eq.MulMulRealPreimageSProbIntegral_MulEqSAndEqA
import Lemma.Random.Integral_MulEqSAndEqA.eq.MulMulRealProbSum_MulT
import Lemma.Random.Integral_MulEqSAndEqAR.eq.MulMulRealPreimageSProbIntegral_Rc
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
import Lemma.Random.MulProbMulTV.eq.MulProbMulTTSum_MulPowW.of.Ne0Real_Preimage.In_Ico
import Lemma.Random.Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico
import Lemma.Random.RealInterPreimageS_PreimageA.eq.MulRealPreimageSProb
import Lemma.Real.Mul_AddMul_MulMul.eq.Add_Mul.of.Ne_0
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
Bellman equation for the action value of the trajectory model:
`γ ** Stack[k](k) @ 𝔼[r[t:] | s[t] = x, a[t] = u]
  = 𝔼[γ * (γ ** Stack[k](k) @ 𝔼[r[t+1:] | s[t+1]]) + r[t] | s[t] = x, a[t] = u]`.
No history-independence hypothesis on the rewards is needed, since the environment of
`PolicyGradient.Model` is a (Markov) MDP.
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
  (h₀ : γ ∈ Set.Ico 0 1)
  (x : S)
  (u : A) :
-- imply
  ∑' k, γ ^ k * ∫ ω, reward (t + k) ω ∂(M θ)[|state t ⁻¹' {x} ∩ action t ⁻¹' {u}] =
    ∫ ω, γ * (∫ ω', ∑' k, γ ^ k * reward (t + 1 + k) ω' ∂(M θ)[|state (t + 1) ⁻¹' {state (t + 1) ω}]) + reward t ω
      ∂(M θ)[|state t ⁻¹' {x} ∩ action t ⁻¹' {u}] := by
-- proof
  classical
  have hVi : ∀ t x, ∫ ω, ∑' k, γ ^ k * reward (t + k) ω ∂(M θ)[|state t ⁻¹' {x}] = M.V θ γ t x :=
    fun t x => (M.V_eq_integral θ γ t x).symm
  show M.Q θ γ t x u = _
  simp only [hVi]
  by_cases hP : (M θ).real (state t ⁻¹' {x}) * M.pol.prob θ x u = 0
  · rw [← RealInterPreimageS_PreimageA.eq.MulRealPreimageSProb] at hP
    have h₂ := cond_eq_zero_of_meas_eq_zero (Eq_0.of.EqReal_0 (M := M) θ hP)
    simp [Model.Q, h₂]
  · have hP₀ : (M θ).real (state t ⁻¹' {x}) ≠ 0 := left_ne_zero_of_mul hP
    have hu : M.pol.prob θ x u ≠ 0 := right_ne_zero_of_mul hP
    rw [Integral.eq.MulMulRealPreimageSProbIntegral_MulEqSAndEqA]
    have h₂ : ∀ ω : ℕ → ℝ × S × A, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) *
        (γ * M.V θ γ (t + 1) (state (t + 1) ω) + reward t ω) =
        γ * ((if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * M.V θ γ (t + 1) (state (t + 1) ω)) +
          (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * reward t ω := fun ω => by ring
    simp_rw [h₂]
    rw [integral_add ((Integrable.of.Measurable (M := M) (fun ω => ((state t ω, action t ω), state (t + 1) ω)) (((Random.Measurable_S t).prodMk (Random.Measurable_A t)).prodMk (Random.Measurable_S (t + 1)))
        θ
        (fun p => (if p.1.1 = x ∧ p.1.2 = u then (1:ℝ) else 0) * M.V θ γ (t + 1) p.2)).const_mul γ)
      (Integrable_Mul_R.of.Measurable (M := M) (fun ω => (state t ω, action t ω)) ((Random.Measurable_S t).prodMk (Random.Measurable_A t)) θ
        (fun p => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0) t),
      integral_const_mul, Integral_MulEqSAndEqA.eq.MulMulRealProbSum_MulT, Integral_MulEqSAndEqAR.eq.MulMulRealPreimageSProbIntegral_Rc, Mul_AddMul_MulMul.eq.Add_Mul.of.Ne_0 hP, Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico (M := M) θ t x u h₀ hP]
    congr 2
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have h₃ := MulProbMulTV.eq.MulProbMulTTSum_MulPowW.of.Ne0Real_Preimage.In_Ico (M := M) θ t x h₀ hP₀ u y
    exact (mul_left_cancel₀ hu h₃).symm


-- created on 2023-03-29
