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
the discounted state value is the policy average of the action values `Q` given by `h₂` (the sympy `Q_def`).
The discount factor is taken in `[0, 1)` (for `γ = 1` the Lean `tsum` of a divergent series is `0`
and the identity fails).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {Q : S → A → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Q x u = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}])
  (x : S) :
-- imply
  ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M θ)[|s t ⁻¹' {x}] =
    ∫ ω, Q x (a t ω) ∂(M θ)[|s t ⁻¹' {x}] := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  classical
  have h₅ : Q = M.Q r s a θ γ t := funext fun x => funext fun u => h₂ x u
  subst h₅
  have hVi : ∀ t x, ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M θ)[|s t ⁻¹' {x}] = M.V r s θ γ t x :=
    fun t x => (M.V_eq_integral r s θ γ t x).symm
  simp only [hVi]
  by_cases hP : (M θ).real (s t ⁻¹' {x}) = 0
  · have h₃ := cond_eq_zero_of_meas_eq_zero (Eq_0.of.EqReal_0 (M := M) θ hP)
    simp only [← hVi t x, h₃, integral_zero_measure]
  · rw [V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) θ t x h₀ h₁ hP, Integral.eq.MulRealPreimageSIntegral_MulEqS h₁]
    have h₃ : ∀ ω, (if s t ω = x then (1:ℝ) else 0) * M.Q r s a θ γ t x (a t ω) =
        ∑ u, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * M.Q r s a θ γ t x u := by
      intro ω
      rw [Finset.sum_eq_single (a t ω) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      by_cases h : s t ω = x <;> simp [h]
    simp_rw [h₃]
    rw [integral_finsetSum _ (fun u _ => Random.Integrable_MulEqSAndEqA h₁ (M := M) θ t x u _)]
    simp_rw [integral_mul_const, Integral_EqSAndEqA.eq.MulRealPreimageSProb h₁]
    rw [Finset.mul_sum]
    have h₄ : ∀ u, ((M θ).real (s t ⁻¹' {x}))⁻¹ *
        ((M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * M.Q r s a θ γ t x u) =
        M.pol.prob θ x u * ((∫ ρ, M.rc (ρ, x, u) ∂(M.env.reward (x, u))) +
          γ * ∑ y, M.T x u y * ∑' k, γ ^ k * M.W θ M.rc k y) := by
      intro u
      rw [mul_assoc, inv_mul_cancel_left₀ hP]
      by_cases hu : M.pol.prob θ x u = 0
      · simp [hu]
      · rw [Random.Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico (M := M) h₀ h₁ θ t x u (mul_ne_zero hP hu)]
    simp_rw [h₄]
    rw [TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico (M := M) h₀ θ x, W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.Abs_R (M := M)) θ x, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun u _ => by ring)


-- created on 2023-03-29
