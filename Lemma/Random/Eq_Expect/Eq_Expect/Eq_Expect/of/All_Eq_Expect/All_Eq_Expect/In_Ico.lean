import Lemma.Random.MEq_Expect.MEq_Expect.MEq_Expect.of.Expect.All_MEq_Expect.All_MEq_Expect.GtInftySup.All_MeasurableJoint.In_Ico
import Lemma.Random.CondExpPow_Id.of.In_Ico
import Lemma.Random.MeasurableJoint.is.Measurable.Measurable
import Lemma.Random.MEqCondExp_Integral.of.Integrable.Measurable
import Lemma.Random.Eq.of.Ne_0.MEq
import sympy.stats.policy_trajectory.gradient
import sympy.stats.cond_expectation
import sympy.core.power
import sympy.vector.Basic
import Lemma.Random.Integrable_G.of.In_Ico
import Lemma.Random.MEqR_Rc
import Lemma.Random.Integrable.of.Measurable
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
import Lemma.Random.NormRc.le.Abs_R
import Lemma.Random.StronglyMeasurableRc
open MeasureTheory ProbabilityTheory PolicyGradient Random


/--
Bellman equation of discrete actions under discrete states
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {Q : ℕ → S → A → ℝ}
  {V : ℕ → S → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₃ : ∀ t («s.bvar» : ℕ → S), V t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  («s.bvar» : ℕ → S)
  («a.bvar» : ℕ → A) :
-- imply
  V t («s.bvar» t) = 𝔼[a : M θ](Q t («s.bvar» t) (a t) | s t = «s.bvar» t) ∧
    V t («s.bvar» t) = 𝔼[r, s : M θ](r t + γ * V (t + 1) (s (t + 1)) | s t = «s.bvar» t) ∧
    Q t («s.bvar» t) («a.bvar» t) = 𝔼[r, s : M θ](r t + γ * V (t + 1) (s (t + 1)) | s t = «s.bvar» t ∧ a t = «a.bvar» t) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  set x := «s.bvar» t
  set u := «a.bvar» t
  have hs : ∀ t, Measurable (s t) := Random.Measurable_S
  have ha : ∀ t, Measurable (a t) := Random.Measurable_A
  have hr : ∀ t, Measurable (r t) := Model.r_meas'
  have hsa : ∀ t, Measurable (fun ω ↦ (s t ω, a t ω)) := fun t ↦
    (hs t).prodMk (ha t)
  have hpa : Measurable (fun ω t ↦ a t ω) := measurable_pi_lambda _ ha
  have hpr : Measurable (fun ω t ↦ r t ω, fun ω t ↦ s t ω) :=
    (measurable_pi_lambda _ hr).prodMk (measurable_pi_lambda _ hs)
  have hpR : Measurable (fun ω t ↦ r t ω) := measurable_pi_lambda _ hr
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hf : Measurable (fun integ : (ℕ → ℝ) × (ℕ → S) ↦ integ.1 t + γ * V (t + 1) (integ.2 (t + 1))) :=
    ((measurable_pi_apply t).comp measurable_fst).add
      (((measurable_of_countable (V (t + 1))).comp ((measurable_pi_apply (t + 1)).comp measurable_snd)).const_mul γ)
  -- `Q`, `V` are the conditional expected returns on the atoms
  have hQ : ∀ t x u, Q t x u = ∫ ω, G γ t ω ∂(M θ)[|(fun ω ↦ (s t ω, a t ω)) ⁻¹' {(x, u)}] := by
    intro t x u
    rw [h₂ t (fun _ ↦ x) (fun _ ↦ u)]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    rfl
  have hV : ∀ t x, V t x = ∫ ω, G γ t ω ∂(M θ)[|s t ⁻¹' {x}] := by
    intro t x
    rw [h₃ t (fun _ ↦ x)]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    rfl
  -- the general lemma, with the clamped (pointwise bounded, a.s. equal) rewards `M.rc (ω t)`
  have hrc : ∀ t, Measurable (fun ω : ℕ → ℝ × S × A ↦ M.rc (ω t)) := fun t ↦
    (Random.StronglyMeasurableRc (M := M)).measurable.comp (measurable_pi_apply t)
  have hR : ∀ t (ω : ℕ → ℝ × S × A), |M.rc (ω t)| ≤ |M.env.R| := fun t ω ↦
    (Real.norm_eq_abs _).symm.trans_le (NormRc.le.Abs_R (M := M) (ω t))
  have hG : ∀ n, (fun ω : ℕ → ℝ × S × A ↦ (γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ ↦ M.rc (ω k))[n:]) =ᵐ[M θ] G γ n :=
    fun n ↦ (ae_all_iff.2 fun k ↦ MEqR_Rc (M := M) θ k).mono fun ω h ↦ by
      exact tsum_congr fun k ↦ congrArg (γ ^ k * ·) (h (n + k)).symm
  have hGi : ∀ n, Integrable (G (S := S) (A := A) γ n) (M θ) := Integrable_G.of.In_Ico (M := M) θ h₀
  have h₅ : ∀ t, (fun ω ↦ Q t (s t ω) (a t ω)) =ᵐ[M θ]
      (M θ)[(fun ω : ℕ → ℝ × S × A ↦ (γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ ↦ M.rc (ω k))[t:]) | MeasurableSpace.comap (fun ω ↦ (s t ω, a t ω)) inferInstance] :=
    fun t ↦ Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun ω ↦ hQ t (s t ω) (a t ω))
      ((MEqCondExp_Integral.of.Integrable.Measurable (hsa t) (hGi t)).symm.trans (condExp_congr_ae (hG t)).symm)
  have h₆ : ∀ t, (fun ω ↦ V t (s t ω)) =ᵐ[M θ]
      (M θ)[(fun ω : ℕ → ℝ × S × A ↦ (γ ^ (id : ℕ → ℕ)) @ (fun k : ℕ ↦ M.rc (ω k))[t:]) | MeasurableSpace.comap (s t) inferInstance] :=
    fun t ↦ Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun ω ↦ hV t (s t ω))
      ((MEqCondExp_Integral.of.Integrable.Measurable (hs t) (hGi t)).symm.trans (condExp_congr_ae (hG t)).symm)
  have h₇ := ((condExp_congr_ae (hG (t + 1))).trans (CondExpPow_Id.of.In_Ico (M := M) (θ := θ) (t := t) h₀)).trans
    (condExp_congr_ae (hG (t + 1))).symm
  have hσ : MeasurableSpace.comap (fun ω : ℕ → ℝ × S × A ↦ ((s t ω, a t ω), s (t + 1) ω)) inferInstance =
      MeasurableSpace.comap (JointRandomSymbol (s t) (JointRandomSymbol (a t) (s (t + 1)))) inferInstance := by
    apply le_antisymm
    ·
      apply Measurable.comap_le
      exact (show Measurable fun p : S × A × S ↦ ((p.1, p.2.1), p.2.2) by fun_prop).comp
        (comap_measurable (JointRandomSymbol (s t) (JointRandomSymbol (a t) (s (t + 1)))))
    ·
      apply Measurable.comap_le
      exact (show Measurable fun p : (S × A) × S ↦ (p.1.1, p.1.2, p.2) by fun_prop).comp
        (comap_measurable fun ω : ℕ → ℝ × S × A ↦ ((s t ω, a t ω), s (t + 1) ω))
  erw [hσ] at h₇
  obtain ⟨h₈, h₉, h₁₀⟩ := MEq_Expect.MEq_Expect.MEq_Expect.of.Expect.All_MEq_Expect.All_MEq_Expect.GtInftySup.All_MeasurableJoint.In_Ico
    (π := M θ) (s := s) (a := a) (r := fun t ω ↦ M.rc (ω t)) (t := t) h₀
    (fun t ↦ Random.MeasurableJoint.of.Measurable.Measurable (hrc t) (Random.MeasurableJoint.of.Measurable.Measurable (hs t) (ha t)))
    ⟨|M.env.R|, Set.forall_mem_range.2 fun ⟨t, ω⟩ ↦ hR t ω⟩ h₅ h₆ h₇
  -- back to the raw rewards
  have hri : Integrable (r t) (M θ) :=
    Integrable.of_bound (hr t).aestronglyMeasurable |M.env.R|
      ((MEqR_Rc (M := M) θ t).mono fun ω (h : r t ω = M.rc (ω t)) ↦ by rw [h]; exact NormRc.le.Abs_R (M := M) _)
  have hF : Integrable (fun ω ↦ r t ω + γ * V (t + 1) (s (t + 1) ω)) (M θ) :=
    hri.add ((Integrable.of.Measurable (M := M) (s (t + 1)) (hs (t + 1)) θ (V (t + 1))).const_mul γ)
  have hFae : (fun ω : ℕ → ℝ × S × A ↦ M.rc (ω t) + γ * V (t + 1) (s (t + 1) ω)) =ᵐ[M θ]
      fun ω ↦ r t ω + γ * V (t + 1) (s (t + 1) ω) :=
    (MEqR_Rc (M := M) θ t).mono fun ω (h : r t ω = M.rc (ω t)) ↦ by dsimp only; rw [h]
  have hQi : Integrable (fun ω ↦ Q t (s t ω) (a t ω)) (M θ) :=
    Integrable.of.Measurable (M := M) (fun ω ↦ (s t ω, a t ω)) (hsa t) θ (fun p ↦ Q t p.1 p.2)
  have hx : ∀ {B : Set (ℕ → ℝ × S × A)} (f : (ℕ → ℝ × S × A) → ℝ), M θ B = 0 → ∫ ω, f ω ∂(M θ)[|B] = 0 :=
    fun f h ↦ by rw [cond_eq_zero_of_meas_eq_zero h, integral_zero_measure]
  refine ⟨?_, ?_, ?_⟩
  ·
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpa.aemeasurable (by fun_prop)]
    if h : M θ (s t ⁻¹' {x}) = 0 then
      rw [hV, hx _ h, hx _ h]
    else
      rw [Eq.of.Ne_0.MEq (u := V t) (v := fun y ↦ ∫ ω, Q t (s t ω) (a t ω) ∂(M θ)[|s t ⁻¹' {y}])
        (h₈.trans (MEqCondExp_Integral.of.Integrable.Measurable (hs t) hQi)) h]
      exact integral_congr_ae ((ae_cond_mem (hs t (measurableSet_singleton x))).mono fun ω hω ↦ by
        dsimp only
        rw [show s t ω = x from hω])
  ·
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpr.aemeasurable hf]
    if h : M θ (s t ⁻¹' {x}) = 0 then
      rw [hV, hx _ h, hx _ h]
    else
      exact Eq.of.Ne_0.MEq (u := V t)
        (v := fun y ↦ ∫ ω, r t ω + γ * V (t + 1) (s (t + 1) ω) ∂(M θ)[|s t ⁻¹' {y}])
        (h₉.trans ((condExp_congr_ae hFae).trans (MEqCondExp_Integral.of.Integrable.Measurable (hs t) hF))) h
  ·
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpr.aemeasurable hf]
    if h : M θ ((fun ω ↦ (s t ω, a t ω)) ⁻¹' {(x, u)}) = 0 then
      rw [hQ, hx _ h]
      exact (hx _ h).symm
    else
      exact Eq.of.Ne_0.MEq (X := fun ω ↦ (s t ω, a t ω)) (u := fun p ↦ Q t p.1 p.2)
        (v := fun p ↦ ∫ ω, r t ω + γ * V (t + 1) (s (t + 1) ω) ∂(M θ)[|(fun ω ↦ (s t ω, a t ω)) ⁻¹' {p}])
        (h₁₀.trans ((condExp_congr_ae hFae).trans (MEqCondExp_Integral.of.Integrable.Measurable (hsa t) hF))) h


-- created on 2023-03-28
-- updated on 2026-10-06
