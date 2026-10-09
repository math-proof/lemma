import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Eq_0.of.EqReal_0
import Lemma.Random.Integrable.of.Measurable
import Lemma.Random.Integrable_Mul_R.of.Measurable
import Lemma.Random.Integral.eq.MulRealPreimageSIntegral_MulEqS
import Lemma.Random.Integral_MulEqS.eq.MulRealSum_MulProbSum_MulT
import Lemma.Random.Integral_MulEqSR_Add.eq.MulRealPreimageSWRc
import Lemma.Random.Measurable_S
import Lemma.Random.MulProbMulTV.eq.MulProbMulTTSum_MulPowW.of.Ne0Real_Preimage.In_Ico
import Lemma.Random.TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico
import Lemma.Random.V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico
import Lemma.Real.Mul_AddMul_MulMul.eq.Add_Mul.of.Ne_0
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
Bellman equation for the state value of the trajectory model:
`γ ** Stack[k](k) @ 𝔼[r[t:] | s[t] = x] = 𝔼[γ * (γ ** Stack[k](k) @ 𝔼[r[t+1:] | s[t+1]]) + r[t] | s[t] = x]`.
No history-independence hypothesis on the rewards is needed, since the environment of
`PolicyGradient.Model` is a (Markov) MDP.
Both sides are `0` when `s[t] = x` has probability `0`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (x : S) :
-- imply
  ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M θ)[|s t ⁻¹' {x}] =
    ∫ ω, γ * (∫ ω', ∑' k, γ ^ k * r (t + 1 + k) ω' ∂(M θ)[|s (t + 1) ⁻¹' {s (t + 1) ω}]) + r t ω
      ∂(M θ)[|s t ⁻¹' {x}] := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  classical
  have hVi : ∀ t x, ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M θ)[|s t ⁻¹' {x}] = M.V r s θ γ t x :=
    fun t x => (M.V_eq_integral r s θ γ t x).symm
  simp only [hVi]
  by_cases hP : (M θ).real (s t ⁻¹' {x}) = 0
  · have h₂ := cond_eq_zero_of_meas_eq_zero (Eq_0.of.EqReal_0 (M := M) θ hP)
    simp only [← hVi t x, h₂, integral_zero_measure]
  · rw [Integral.eq.MulRealPreimageSIntegral_MulEqS h₁]
    have h₂ : ∀ ω : ℕ → ℝ × S × A, (if s t ω = x then (1:ℝ) else 0) *
        (γ * M.V r s θ γ (t + 1) (s (t + 1) ω) + r t ω) =
        γ * ((if s t ω = x then (1:ℝ) else 0) * M.V r s θ γ (t + 1) (s (t + 1) ω)) +
          (if s t ω = x then (1:ℝ) else 0) * r t ω := fun ω => by ring
    simp_rw [h₂]
    rw [integral_add ((Integrable.of.Measurable (M := M) (fun ω => (s t ω, s (t + 1) ω)) ((Random.Measurable_S h₁ t).prodMk (Random.Measurable_S h₁ (t + 1)))
        θ
        (fun p => (if p.1 = x then (1:ℝ) else 0) * M.V r s θ γ (t + 1) p.2)).const_mul γ)
      (Integrable_Mul_R.of.Measurable h₁ (M := M) (s t) (Random.Measurable_S h₁ t) θ (fun y => if y = x then (1:ℝ) else 0) t),
      integral_const_mul]
    have h₃ := Integral_MulEqSR_Add.eq.MulRealPreimageSWRc (M := M) h₁ θ t 0 x
    simp only [add_zero] at h₃
    have h₄ := Integral_MulEqS.eq.MulRealSum_MulProbSum_MulT h₁ (M := M) θ t x (M.V r s θ γ (t + 1))
    rw [h₃, h₄, V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) θ t x h₀ h₁ hP, TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico (M := M) h₀ θ x, Mul_AddMul_MulMul.eq.Add_Mul.of.Ne_0 hP]
    congr 2
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => (MulProbMulTV.eq.MulProbMulTTSum_MulPowW.of.Ne0Real_Preimage.In_Ico (M := M) h₀ h₁ θ t x hP u y).symm)


-- created on 2023-03-27
