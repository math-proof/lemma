import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral.eq.MulMulRealPreimageSProbIntegral_MulEqSAndEqA
import Lemma.Random.Integral_MulEqSAndEqAR.eq.MulMulRealPreimageSProbIntegral_Rc
import Lemma.Random.Integral_MulEqSAndEqAR.eq.MulMulRealProbSum_MulTW
import Lemma.Random.Summable_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Summable_MulPowWRc.of.In_Ico
import Lemma.Real.TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
On a reachable state-action pair: `Q θ γ t x u = 𝔼[rc | x, u] + γ * ∑ y, T(x, u, y) * ∑' k, γ ^ k * W θ rc k y`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (u : A)
  (hγ : γ ∈ Set.Ico 0 1)
  (hP : (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u ≠ 0) :
-- imply
  M.Q θ γ t x u = (∫ ρ, M.rc (ρ, x, u) ∂(M.env.reward (x, u))) +
    γ * ∑ y, M.T x u y * ∑' k, γ ^ k * M.W θ M.rc k y := by
-- proof
  unfold Model.Q
  rw [(Summable_MulPowIntegral_R_Add.of.In_Ico (M := M) hγ θ _ t).tsum_eq_zero_add]
  have h0 : ∫ ω, r (t + 0) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] =
      ∫ ρ, M.rc (ρ, x, u) ∂(M.env.reward (x, u)) := by
    rw [Integral.eq.MulMulRealPreimageSProbIntegral_MulEqSAndEqA, add_zero, Integral_MulEqSAndEqAR.eq.MulMulRealPreimageSProbIntegral_Rc, inv_mul_cancel_left₀ hP]
  have hk : ∀ k, ∫ ω, r (t + (k + 1)) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] =
      ∑ y, M.T x u y * M.W θ M.rc k y := by
    intro k; rw [Integral.eq.MulMulRealPreimageSProbIntegral_MulEqSAndEqA, Integral_MulEqSAndEqAR.eq.MulMulRealProbSum_MulTW, inv_mul_cancel_left₀ hP]
  rw [h0, pow_zero, one_mul]
  simp_rw [hk, pow_succ, mul_comm _ γ, mul_assoc γ]
  rw [tsum_mul_left, TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow _ (fun y => Summable_MulPowWRc.of.In_Ico (M := M) hγ θ y) _]


-- created on 2026-10-07
