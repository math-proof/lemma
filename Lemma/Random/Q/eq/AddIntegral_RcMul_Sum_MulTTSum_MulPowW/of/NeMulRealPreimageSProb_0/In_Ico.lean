import sympy.stats.policy_trajectory
import sympy.stats.cond_expectation
import sympy.Basic
import Lemma.Random.Integral.eq.MulMulRealPreimageProbIntegral_MulEqAndEq.of.All_Eq
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Integral_MulEqAndEq.eq.MulMulRealPreimageProbIntegral_Rc.of.All_Eq
import Lemma.Random.Integral_MulEqAndEq.eq.MulMulRealProbSum_MulTW.of.All_Eq
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.Summable_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Summable_MulPowWRc.of.In_Ico
import Lemma.Real.TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
On a reachable state-action pair: `Q θ γ t x u = 𝔼[rc | x, u] + γ * ∑ y, T(x, u, y) * ∑' k, γ ^ k * W θ rc k y`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (u : A)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u ≠ 0) :
-- imply
  let Q (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u);
  Q θ t x u = (∫ ρ, M.rc (ρ, x, u) ∂(M.env.reward (x, u))) +
    γ * ∑ y, (M.env.trans (x, u)).real {y} * ∑' k, γ ^ k * M.W θ M.rc k y := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  simp only [Expectation.asRV_process]
  rw [Expectation.condEvent_eq_integral hpR.aemeasurable hfG]
  have hpre : (s t, a t) ⁻¹' {(x, u)} = s t ⁻¹' {x} ∩ a t ⁻¹' {u} := by
    ext ω
    simp [JointRandomSymbol]
  rw [hpre]
  show ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] = _
  rw [Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ h₁ θ _ t]
  rw [(Summable_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ h₁ θ _ t).tsum_eq_zero_add]
  have h0 : ∫ ω, r (t + 0) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] =
      ∫ ρ, M.rc (ρ, x, u) ∂(M.env.reward (x, u)) := by
    rw [Integral.eq.MulMulRealPreimageProbIntegral_MulEqAndEq.of.All_Eq h₁, add_zero, Integral_MulEqAndEq.eq.MulMulRealPreimageProbIntegral_Rc.of.All_Eq h₁, inv_mul_cancel_left₀ h₂]
  have hk : ∀ k, ∫ ω, r (t + (k + 1)) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] =
      ∑ y, (M.env.trans (x, u)).real {y} * M.W θ M.rc k y := by
    intro k; rw [Integral.eq.MulMulRealPreimageProbIntegral_MulEqAndEq.of.All_Eq h₁, Integral_MulEqAndEq.eq.MulMulRealProbSum_MulTW.of.All_Eq h₁, inv_mul_cancel_left₀ h₂]
  rw [h0, pow_zero, one_mul]
  simp_rw [hk, pow_succ, mul_comm _ γ, mul_assoc γ]
  rw [tsum_mul_left, TSum_MulPowSum_Mul.eq.Sum_Mul_TSum_MulPow.of.All_Summable_MulPow _ (fun y => Summable_MulPowWRc.of.In_Ico (M := M) h₀ θ y) _]


-- created on 2026-10-07
-- updated on 2026-10-10
