import sympy.stats.policy_trajectory
import sympy.stats.cond_expectation
import sympy.Basic
import Lemma.Random.Eq_0.of.EqReal_0
import Lemma.Random.Integrable.of.Measurable
import Lemma.Random.Integrable_Mul_R.of.Measurable
import Lemma.Random.Integral.eq.MulMulRealPreimageProbIntegral_MulEqAndEq.of.All_Eq
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Integral_MulEqAndEq.eq.MulMulRealProbSum_MulT.of.All_Eq
import Lemma.Random.Integral_MulEqAndEq.eq.MulMulRealPreimageProbIntegral_Rc.of.All_Eq
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.MulProbMulTV.eq.MulProbMulTTSum_MulPowW.of.Ne0Real_Preimage.In_Ico
import Lemma.Random.Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico
import Lemma.Random.RealInterPreimage_Preimage.eq.MulRealPreimageProb.of.All_Eq
import Lemma.Random.V.eq.Integral.of.Measurable
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
  (x : S)
  (u : A) :
-- imply
  ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] =
    ∫ ω, γ * (∫ ω', ∑' k, γ ^ k * r (t + 1 + k) ω' ∂(M θ)[|s (t + 1) ⁻¹' {s (t + 1) ω}]) + r t ω
      ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  classical
  let Qloc (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hpre : (s t, a t) ⁻¹' {(x, u)} = s t ⁻¹' {x} ∩ a t ⁻¹' {u} := by
    ext ω
    simp [JointRandomSymbol]
  have hQtsum : Qloc θ t x u =
      ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] := by
    simp only [Qloc, Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable hfG, hpre]
    show ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] = _
    exact Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ h₁ θ _ t
  rw [← hQtsum]
  let Vloc (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)
  have hVi : ∀ t x, ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M θ)[|s t ⁻¹' {x}] = Vloc θ t x :=
    fun t x => (V.eq.Integral.of.Measurable (M := M) hpR θ γ t x).symm
  simp only [hVi]
  if hP : (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u = 0 then
    rw [← RealInterPreimage_Preimage.eq.MulRealPreimageProb.of.All_Eq h₁] at hP
    have h₂ := cond_eq_zero_of_meas_eq_zero (Eq_0.of.EqReal_0 (M := M) θ hP)
    rw [hQtsum]
    show ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] = _
    simp [h₂]
  else
    have hP₀ : (M θ).real (s t ⁻¹' {x}) ≠ 0 := left_ne_zero_of_mul hP
    have hu : M.pol.prob θ x u ≠ 0 := right_ne_zero_of_mul hP
    rw [Integral.eq.MulMulRealPreimageProbIntegral_MulEqAndEq.of.All_Eq h₁]
    have h₂ : ∀ ω : ℕ → ℝ × S × A, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
        (γ * Vloc θ (t + 1) (s (t + 1) ω) + r t ω) =
        γ * ((if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * Vloc θ (t + 1) (s (t + 1) ω)) +
          (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r t ω := fun ω => by ring
    simp_rw [h₂]
    rw [integral_add ((Integrable.of.Measurable (M := M) (fun ω => ((s t ω, a t ω), s (t + 1) ω)) (((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)).prodMk (Random.Measurable.of.All_Eq.snd.fst h₁ (t + 1)))
        θ
        (fun p => (if p.1.1 = x ∧ p.1.2 = u then (1:ℝ) else 0) * Vloc θ (t + 1) p.2)).const_mul γ)
      (Integrable_Mul_R.of.Measurable h₁ (M := M) (fun ω => (s t ω, a t ω)) ((Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)) θ
        (fun p => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0) t),
      integral_const_mul, Integral_MulEqAndEq.eq.MulMulRealProbSum_MulT.of.All_Eq h₁, Integral_MulEqAndEq.eq.MulMulRealPreimageProbIntegral_Rc.of.All_Eq h₁, Mul_AddMul_MulMul.eq.Add_Mul.of.Ne_0 hP]
    apply (Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico (M := M) θ t x u h₀ h₁ hP).trans
    congr 2
    refine Finset.sum_congr rfl (fun y _ => ?_)
    apply Eq.symm
    apply mul_left_cancel₀ hu
    apply MulProbMulTV.eq.MulProbMulTTSum_MulPowW.of.Ne0Real_Preimage.In_Ico (M := M) θ t x h₀ h₁ hP₀ u y


-- created on 2023-03-29
