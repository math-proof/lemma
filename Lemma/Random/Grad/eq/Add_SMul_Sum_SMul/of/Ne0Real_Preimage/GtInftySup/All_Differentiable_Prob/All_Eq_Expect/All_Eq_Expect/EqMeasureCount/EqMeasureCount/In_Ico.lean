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
the gradient of the Bellman equations of extract_QVA on a reachable state s.bvar[t] (h₇ : Pr(s[t] = s.bvar[t]) ≠ 0).
It is the discrete/discrete case next to the continuous-state/discrete-action
`Random.GradVk.eq.Add_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Differentiable_Prob.In_Ico`,
the continuous/continuous
`Random.GradVkd.eq.AddIntegral_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico`
and the discrete-state/continuous-action
`Random.GradVkd.eq.AddIntegral_SMul_Sum_SMul.of.All_EqReal.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico`
versions. The reference measures of `S` and `A` are the counting measures (h₁, h₂), so the conditional probabilities are
elementary: Pr(a[t] = u | s[t] = x) = π_θ(u | x) on reachable states and Pr(s[t+1] = y | s[t] = x) = P1 θ x y.
h₃, h₄: Q, V are the action and state values, i.e. the conditional expectations of the discounted return
`γ ** Stack[k](k) @ r[t:]` given `s[t] = x, a[t] = u` (resp. `s[t] = x`), as functions of the weights θ;
h₅, h₆: θ ↦ π_θ(u | x) is differentiable with a bounded gradient.
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
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (h₂ : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₃ : let r := @reward S A; ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q θ t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | state t = «s.bvar» t ∧ action t = «a.bvar» t))
  (h₄ : let r := @reward S A; ∀ θ t («s.bvar» : ℕ → S), V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | state t = «s.bvar» t))
  (h₅ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₆ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₇ : (M θ).real (state t ⁻¹' {«s.bvar» t}) ≠ 0) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (action (S := S) (A := A) t, state (S := S) (A := A) t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable_A t).prodMk (Random.Measurable_S t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [h₂, h₁, Measure.Count.eq.ProdCountS])
  have : ∀ θ t, SinglePSpace (M θ) (state (S := S) (A := A) (t + 1), state (S := S) (A := A) t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
      (Random.Measurable_S (t + 1)) (Random.Measurable_S t) h₁ h₁
  ∇[θ] V θ t («s.bvar» t) =
    ∑ «a.bvar» t, Q θ t («s.bvar» t) («a.bvar» t) •
        ∇[θ] (ℙ[M θ]((action t) = («a.bvar» t) | (state t) = («s.bvar» t)) : ℝ) +
      γ • (∑ «s.bvar» (t + 1), (ℙ[M θ]((state (t + 1)) = («s.bvar» (t + 1)) | (state t) = («s.bvar» t)) : ℝ) •
        ∇[θ] V θ (t + 1) («s.bvar» (t + 1))) := by
-- proof
  intro hP hPs
  have hpR : Measurable (fun ω t ↦ reward (S := S) (A := A) t ω) := measurable_pi_lambda _ (Model.r_meas' (S := S) (A := A))
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hQ : Q = fun θ => M.Q θ γ := funext fun θ => funext fun t => funext fun x => funext fun u => by
    rw [h₃ θ t (fun _ ↦ x) (fun _ ↦ u)]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    have hpre : JointRandomSymbol (state (S := S) (A := A) t) (action (S := S) (A := A) t) ⁻¹' {(x, u)} =
        state t ⁻¹' {x} ∩ action t ⁻¹' {u} := by
      ext ω
      simp [JointRandomSymbol, Prod.ext_iff]
    rw [hpre]
    apply Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ θ _ t
  have hV : V = fun θ => M.V θ γ := funext fun θ => funext fun t => funext fun x => by
    rw [h₄ θ t (fun _ ↦ x), M.V_eq_integral θ γ t x]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    rfl
  subst hQ hV
  classical
  beta_reduce
  set x := «s.bvar» t
  have hπ : ∀ u, ∇[θ] (ℙ[M θ]((action t) = u | (state t) = x) : ℝ) = ∇[θ] M.pol.prob θ x u := by
    intro u
    refine Filter.EventuallyEq.gradient_eq ?_
    filter_upwards [(Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₅ h₆ t x θ).continuousAt.eventually_ne h₇] with θ' h
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ h₂ (hP θ' t) h, ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
  simp_rw [hπ]
  rw [GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico h₀ h₅ h₆ h₇]
  have hP1 : ∀ y, (ℙ[M θ]((state (t + 1)) = y | (state t) = x) : ℝ) = M.P1 θ x y := by
    intro y
    rw [ProbCond.eq.Div.of.Eq_Count.Eq_Count (π := M θ) (x := state (S := S) (A := A) (t + 1)) (y := state (S := S) (A := A) t) h₁ h₁ y x,
      ENNReal.toReal_div, ← RealPreimageSPreimageS_Add_1.eq.P1.of.Ne0Real_Preimage (M := M) θ t x y h₇,
      measureReal_def, cond_apply (Random.Measurable_S t (measurableSet_singleton x)),
      ENNReal.toReal_mul, ENNReal.toReal_inv, mul_comm, div_eq_mul_inv]
    congr 3
    apply Set.inter_comm
  simp_rw [hP1]


-- created on 2026-10-07
