import sympy.stats.policy_trajectory
import sympy.functions.elementary.miscellaneous
import sympy.stats.cond_expectation
import sympy.Basic
import Lemma.Random.Eq_0.of.EqReal_0
import Lemma.Random.Integrable_MulEqAndEq.of.All_Eq
import Lemma.Random.Integral.eq.MulRealPreimageSIntegral_MulEqS
import Lemma.Random.Integral_EqAndEq.eq.MulRealPreimageProb.of.All_Eq
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.NormRc.le.AbsR
import Lemma.Random.Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico
import Lemma.Random.StronglyMeasurableRc
import Lemma.Random.TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico
import Lemma.Random.V.eq.Integral.of.Measurable
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
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hpre : ∀ x u, (s t, a t) ⁻¹' {(x, u)} = s t ⁻¹' {x} ∩ a t ⁻¹' {u} := fun x u => by
    ext ω
    simp [JointRandomSymbol]
  let Qloc (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
  have h₅ : Q = Qloc := funext fun x => funext fun u => by
    rw [h₂ x u]
    simp only [Qloc, Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable hfG, hpre x u]
    show ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] =
      ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}]
    exact (Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ h₁ θ _ t).symm
  subst h₅
  let Vloc (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)
  have hVi : ∀ t x, ∫ ω, ∑' k, γ ^ k * r (t + k) ω ∂(M θ)[|s t ⁻¹' {x}] = Vloc θ t x :=
    fun t x => (V.eq.Integral.of.Measurable (M := M) hpR θ γ t x).symm
  simp only [hVi]
  if hP : (M θ).real (s t ⁻¹' {x}) = 0 then
    have h₃ := cond_eq_zero_of_meas_eq_zero (Eq_0.of.EqReal_0 (M := M) θ hP)
    simp only [← hVi t x, h₃, integral_zero_measure]
  else
    let rc (z : ℝ × S × A) : ℝ := clip z.1 (-M.env.R) M.env.R
    have hVsum : Vloc θ t x = ∑' k, γ ^ k * ∫ z, M.Kf θ rc k z ∂(M.stageK θ x) := by
      simpa [Vloc] using V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) θ t x h₀ h₁ hP
    rw [hVsum, Integral.eq.MulRealPreimageSIntegral_MulEqS h₁]
    have h₃ : ∀ ω, (if s t ω = x then (1:ℝ) else 0) * Qloc x (a t ω) =
        ∑ u, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * Qloc x u := by
      intro ω
      rw [Finset.sum_eq_single (a t ω) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      by_cases h : s t ω = x <;> simp [h]
    simp_rw [h₃]
    rw [integral_finsetSum _ (fun u _ => Integrable_MulEqAndEq.of.All_Eq h₁ (M := M) θ t x u _)]
    simp_rw [integral_mul_const, Integral_EqAndEq.eq.MulRealPreimageProb.of.All_Eq h₁]
    rw [Finset.mul_sum]
    have h₄ : ∀ u, ((M θ).real (s t ⁻¹' {x}))⁻¹ *
        ((M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * Qloc x u) =
        M.pol.prob θ x u * ((∫ ρ, rc (ρ, x, u) ∂(M.env.reward (x, u))) +
          γ * ∑ y, (M.env.trans (x, u)).real {y} * ∑' k, γ ^ k * ∫ z, M.Kf θ rc k z ∂(M.stageK θ y)) := by
      intro u
      rw [mul_assoc, inv_mul_cancel_left₀ hP]
      if hu : M.pol.prob θ x u = 0 then
        simp [hu]
      else
        refine congrArg (M.pol.prob θ x u * ·) ?_
        apply Q.eq.AddIntegral_RcMul_Sum_MulTTSum_MulPowW.of.NeMulRealPreimageSProb_0.In_Ico (M := M) θ t x u h₀ h₁ (mul_ne_zero hP hu)
    simp_rw [h₄]
    rw [TSum_MulPowW.eq.AddWMul_Sum_MulProbSum_MulTTSum_MulPowW.of.In_Ico (M := M) h₀ θ x]
    rw [show M.Kf θ rc 0 = rc from funext fun w => rfl]
    rw [W0.eq.Sum_MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableRc (M := M)) (NormRc.le.AbsR (M := M)) θ x, Finset.mul_sum, ← Finset.sum_add_distrib]
    have hK : ∀ k z, M.Kf θ (fun z => clip z.1 (-M.env.R) M.env.R) k z = M.Kf θ rc k z := fun k z => by simp [rc]
    simp_rw [hK]
    apply Finset.sum_congr rfl
    intro u _
    ring


-- created on 2023-03-29
-- updated on 2026-10-11

