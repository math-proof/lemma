import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Eq_0.of.EqReal_0
import Lemma.Random.Integrable_MulEqSAndEqA
import Lemma.Random.Integral.eq.MulRealPreimageSIntegral_MulEqS
import Lemma.Random.Integral_EqSAndEqA.eq.MulRealPreimageSProb
import Lemma.Random.NormRc.le.Abs_R
import Lemma.Random.Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico
import Lemma.Random.V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico
import Lemma.Random.W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
`γ ** Stack[k](k) @ 𝔼[r[t:] | s[t] = x] = 𝔼_{a[t] ∼ π}[Q(s[t] = x, a[t]) | s[t] = x]`:
the discounted state value is the policy average of the action values `Q` given by `h₁` (the sympy `Q_def`).
The discount factor is taken in `[0, 1)` (for `γ = 1` the Lean `tsum` of a divergent series is `0`
and the identity fails).
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {Q : S → A → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ x u, Q x u = ∑' k, γ ^ k * ∫ ω, reward (t + k) ω ∂(M θ)[|state t ⁻¹' {x} ∩ action t ⁻¹' {u}])
  (x : S) :
-- imply
  ∫ ω, ∑' k, γ ^ k * reward (t + k) ω ∂(M θ)[|state t ⁻¹' {x}] =
    ∫ ω, Q x (action t ω) ∂(M θ)[|state t ⁻¹' {x}] := by
-- proof
  classical
  have h₂ : Q = M.Q θ γ t := funext fun x => funext fun u => h₁ x u
  subst h₂
  have hVi : ∀ t x, ∫ ω, ∑' k, γ ^ k * reward (t + k) ω ∂(M θ)[|state t ⁻¹' {x}] = M.V θ γ t x :=
    fun t x => (M.V_eq_integral θ γ t x).symm
  simp only [hVi]
  by_cases hP : (M θ).real (state t ⁻¹' {x}) = 0
  · have h₃ := cond_eq_zero_of_meas_eq_zero (Eq_0.of.EqReal_0 (M := M) θ hP)
    simp [M.V_eq_integral, h₃]
  · rw [V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) θ t x h₀ hP, Integral.eq.MulRealPreimageSIntegral_MulEqS]
    have h₃ : ∀ ω, (if state t ω = x then (1:ℝ) else 0) * M.Q θ γ t x (action t ω) =
        ∑ u, (if state t ω = x ∧ action t ω = u then (1:ℝ) else 0) * M.Q θ γ t x u := by
      intro ω
      rw [Finset.sum_eq_single (action t ω) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      by_cases h : state t ω = x <;> simp [h]
    simp_rw [h₃]
    rw [integral_finsetSum _ (fun u _ => Random.Integrable_MulEqSAndEqA (M := M) θ t x u _)]
    simp_rw [integral_mul_const, Integral_EqSAndEqA.eq.MulRealPreimageSProb]
    rw [Finset.mul_sum]
    have h₄ : ∀ u, ((M θ).real (state t ⁻¹' {x}))⁻¹ *
        ((M θ).real (state t ⁻¹' {x}) * M.pol.prob θ x u * M.Q θ γ t x u) =
        M.pol.prob θ x u * ((∫ ρ, M.rc (ρ, x, u) ∂(M.env.reward (x, u))) +
          γ * ∑ y, M.T x u y * ∑' k, γ ^ k * M.W θ M.rc k y) := by
      intro u
      rw [mul_assoc, inv_mul_cancel_left₀ hP]
      by_cases hu : M.pol.prob θ x u = 0
      · simp [hu]
      · rw [Random.Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico (M := M) θ t x u h₀ (mul_ne_zero hP hu)]
    simp_rw [h₄]
    rw [TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico (M := M) h₀ θ x, W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) θ x, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => by ring)


-- created on 2023-03-29
