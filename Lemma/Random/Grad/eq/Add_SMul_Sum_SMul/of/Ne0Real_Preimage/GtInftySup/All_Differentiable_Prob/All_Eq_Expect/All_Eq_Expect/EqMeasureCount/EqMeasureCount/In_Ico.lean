import Lemma.Random.GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico
import sympy.stats.cond_expectation
import sympy.core.power
import sympy.concrete.summations
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count
import Lemma.Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
import Lemma.Random.RealPreimageSPreimageS_Add_1.eq.P1.of.Ne0Real_Preimage
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Topology Random
open scoped ENNReal.ToRealCoe


/--
Policy-gradient recursion with a discrete (finite) state space and a discrete (finite) action space:
∇V(s[t] = s.bvar[t]) = ∑ a.bvar[t], Q(s.bvar[t], a.bvar[t]) • ∇Pr(a[t] = a.bvar[t] | s[t] = s.bvar[t]) + γ • ∑ s.bvar[t+1], Pr(s[t+1] = s.bvar[t+1] | s[t] = s.bvar[t]) • ∇V(s[t+1] = s.bvar[t+1]),
the gradient of the Bellman equations of extract_QVA on a reachable state s.bvar[t] (h₈ : Pr(s[t] = s.bvar[t]) ≠ 0).
It is the discrete/discrete case next to the continuous-state/discrete-action
`Random.GradVk.eq.Add_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Differentiable_Prob.In_Ico`,
the continuous/continuous
`Random.GradVkd.eq.AddIntegral_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico`
and the discrete-state/continuous-action
`Random.GradVkd.eq.AddIntegral_SMul_Sum_SMul.of.All_EqReal.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico`
versions. The reference measures of `S` and `A` are the counting measures (h₂, h₃), so the conditional probabilities are
elementary: Pr(a[t] = u | s[t] = x) = π_θ(u | x) on reachable states and Pr(s[t+1] = y | s[t] = x) = P1 θ x y.
h₄, h₅: Q, V are the action and state values, i.e. the conditional expectations of the discounted return
`γ ** Stack[k](k) @ r[t:]` given `s[t] = x, a[t] = u` (resp. `s[t] = x`), as functions of the weights θ;
h₆, h₇: θ ↦ π_θ(u | x) is differentiable with a bounded gradient.
The proof identifies Q, V with `M.Q`, `M.V` and applies
`Random.GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
  {«s.bvar» : ℕ → S}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (h₃ : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₄ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q θ t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₅ : ∀ θ t («s.bvar» : ℕ → S), V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₆ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₇ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₈ : (M θ).real (s t ⁻¹' {«s.bvar» t}) ≠ 0) :
-- imply
  have hs : ∀ t, Measurable (s t) := fun t ↦ by
    rw [show s t = fun ω ↦ (ω t).2.1 from funext fun ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm]
    exact (measurable_pi_apply t).snd.fst
  have ha : ∀ t, Measurable (a t) := fun t ↦ by
    rw [show a t = fun ω ↦ (ω t).2.2 from funext fun ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm]
    exact (measurable_pi_apply t).snd.snd
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((ha t).prodMk (hs t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [h₃, h₂, Measure.Count.eq.ProdCountS])
  have : ∀ θ t, SinglePSpace (M θ) (s (t + 1), s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable (hs (t + 1)) (hs t) h₂ h₂
  ∇[θ] V θ t («s.bvar» t) =
    ∑ «a.bvar» t, Q θ t («s.bvar» t) («a.bvar» t) •
        ∇[θ] (ℙ[M θ]((a t) = («a.bvar» t) | (s t) = («s.bvar» t)) : ℝ) +
      γ • (∑ «s.bvar» (t + 1), (ℙ[M θ]((s (t + 1)) = («s.bvar» (t + 1)) | (s t) = («s.bvar» t)) : ℝ) •
        ∇[θ] V θ (t + 1) («s.bvar» (t + 1))) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  intro hs ha hP hPs
  have hpR : Measurable (fun ω t ↦ r t ω) := measurable_pi_lambda _ (Model.r_meas' (S := S) (A := A))
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hQ : Q = fun θ => M.Q θ γ := funext fun θ => funext fun t => funext fun x => funext fun u => by
    rw [h₄ θ t (fun _ ↦ x) (fun _ ↦ u)]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    have hpre : JointRandomSymbol (s t) (a t) ⁻¹' {(x, u)} =
        s t ⁻¹' {x} ∩ a t ⁻¹' {u} := by
      ext ω
      simp [JointRandomSymbol, Prod.ext_iff]
    rw [hpre]
    apply Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ θ _ t
  have hV : V = fun θ => M.V θ γ := funext fun θ => funext fun t => funext fun x => by
    rw [h₅ θ t (fun _ ↦ x), M.V_eq_integral θ γ t x]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    rfl
  subst hQ hV
  classical
  beta_reduce
  set x := «s.bvar» t
  have hπ : ∀ u, ∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ) = ∇[θ] M.pol.prob θ x u := by
    intro u
    refine Filter.EventuallyEq.gradient_eq ?_
    filter_upwards [(Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₆ h₇ t x θ).continuousAt.eventually_ne h₈] with θ' h
    erw [ProbCond.eq.OfRealPol.of.Ne_0 h₂ h₃ (hP θ' t) h, ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
  simp only [s, a] at hπ
  simp_rw [hπ]
  rw [GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico h₀ h₆ h₇ h₈]
  have hP1 : ∀ y, (ℙ[M θ]((s (t + 1)) = y | (s t) = x) : ℝ) = M.P1 θ x y := by
    intro y
    rw [ProbCond.eq.Div.of.Eq_Count.Eq_Count (π := M θ) (x := s (t + 1)) (y := s t) h₂ h₂ y x,
      ENNReal.toReal_div, ← RealPreimageSPreimageS_Add_1.eq.P1.of.Ne0Real_Preimage (M := M) θ t x y h₈,
      measureReal_def]
    erw [cond_apply (hs t (measurableSet_singleton x))]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, mul_comm, div_eq_mul_inv]
    congr 3
    apply Set.inter_comm
  simp only [s] at hP1
  simp_rw [hP1]


-- created on 2026-10-07
