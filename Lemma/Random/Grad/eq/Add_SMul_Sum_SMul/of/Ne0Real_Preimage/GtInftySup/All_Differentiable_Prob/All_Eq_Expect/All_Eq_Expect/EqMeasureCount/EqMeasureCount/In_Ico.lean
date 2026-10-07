import Lemma.Random.GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico
import sympy.stats.cond_expectation
import sympy.core.power
import sympy.concrete.summations
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count
import Lemma.Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
import Lemma.Random.RealPreimageSPreimageS_Add_1.eq.P1.of.Ne0Real_Preimage
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random
open scoped ENNReal.ToRealCoe


/--
Policy-gradient recursion: on a reachable state «s.bvar» t (h₅ : Pr(s[t] = s.bvar[t]) ≠ 0),
∇V(s[t] = s.bvar[t]) = ∑ a.bvar[t], Q(s.bvar[t], a.bvar[t]) • ∇π(a.bvar[t] | s.bvar[t]) + γ • ∑ s.bvar[t+1], Pr(s[t+1] = s.bvar[t+1] | s[t] = s.bvar[t]) • ∇V(s[t+1] = s.bvar[t+1]),
the gradient of the Bellman equations of extract_QVA. Q, V are the action and state values
(h₁, h₂, the sympy Q_def, V_def) as functions of the weights θ; h₃, h₄: θ ↦ π_θ(u | x) is differentiable with a bounded gradient.
Cond.Prob.of.Cond.weighted is definitional here: every probability is taken under M θ.
Densities are taken w.r.t. the counting measures (hS, hA), so
ℙ[M θ](a[t] = u | s[t] = x) is the policy π_θ(u | x) at reachable states (OfRealPol);
h₃/h₄ stay as M.pol.prob so they apply GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico definitionally (simp/rfl bridge via OfRealPol).
h₁/h₂ match Random.…In_Ico (with an outer θ binder). Applying that lemma yields the
Bellman identities, not the ∇ goal; the proof therefore reuses its Q = M.Q / V = M.V
identification, then finishes with GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico.
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
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₁ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q θ t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₂ : ∀ θ t («s.bvar» : ℕ → S), V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₃ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₄ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₅ : (M θ).real (s t ⁻¹' {«s.bvar» t}) ≠ 0) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a (S := S) (A := A) t, s (S := S) (A := A) t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((a_meas t).prodMk (s_meas t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [hA, hS, Measure.Count.eq.ProdCountS])
  have : ∀ θ t, SinglePSpace (M θ) (s (S := S) (A := A) (t + 1), s (S := S) (A := A) t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
      (s_meas (t + 1)) (s_meas t) hS hS
  ∇[θ] V θ t («s.bvar» t) =
    ∑ «a.bvar» t, Q θ t («s.bvar» t) («a.bvar» t) •
        ∇[θ] (ℙ[M θ]((a t) = («a.bvar» t) | (s t) = («s.bvar» t)) : ℝ) +
      γ • (∑ «s.bvar» (t + 1), (ℙ[M θ]((s (t + 1)) = («s.bvar» (t + 1)) | (s t) = («s.bvar» t)) : ℝ) •
        ∇[θ] V θ (t + 1) («s.bvar» (t + 1))) := by
-- proof
  intro hP hPs
  -- In_Ico-style identification Q = fun θ => M.Q θ γ, V = fun θ => M.V θ γ
  -- (In_Ico.main itself is the Bellman equation, not usable for this ∇ goal).
  have hr : ∀ t, Measurable (r (S := S) (A := A) t) := Model.r_meas' (S := S) (A := A)
  have hpR : Measurable (fun ω t ↦ r (S := S) (A := A) t ω) := measurable_pi_lambda _ hr
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hQ : Q = fun θ => M.Q θ γ := funext fun θ => funext fun t => funext fun x => funext fun u => by
    rw [h₁ θ t (fun _ ↦ x) (fun _ ↦ u)]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    have hpre : JointRandomSymbol (s (S := S) (A := A) t) (a (S := S) (A := A) t) ⁻¹' {(x, u)} =
        s t ⁻¹' {x} ∩ a t ⁻¹' {u} := by
      ext ω; simp [JointRandomSymbol, Prod.ext_iff]
    rw [hpre]
    exact Model.integral_G_cond M θ h₀ _ t
  have hV : V = fun θ => M.V θ γ := funext fun θ => funext fun t => funext fun x => by
    rw [h₂ θ t (fun _ ↦ x), M.V_eq_integral θ γ t x]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    rfl
  subst hQ hV
  classical
  beta_reduce
  set x := «s.bvar» t
  have hπ : ∀ u, ∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ) = ∇[θ] M.pol.prob θ x u := by
    intro u
    have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {x})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₃ h₄ t x θ).continuousAt
    refine Filter.EventuallyEq.gradient_eq ?_
    filter_upwards [hc.eventually_ne h₅] with θ' h
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 hS hA (hP θ' t) h,
      ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
  simp_rw [hπ]
  rw [GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico h₀ h₃ h₄ h₅]
  have hP1 : ∀ y, (ℙ[M θ]((s (t + 1)) = y | (s t) = x) : ℝ) = M.P1 θ x y := by
    intro y
    have hDiv := ProbCond.eq.Div.of.Eq_Count.Eq_Count (π := M θ)
      (x := s (S := S) (A := A) (t + 1)) (y := s (S := S) (A := A) t) hS hS y x
    rw [hDiv, ENNReal.toReal_div, ← RealPreimageSPreimageS_Add_1.eq.P1.of.Ne0Real_Preimage (M := M) θ t x y h₅]
    rw [measureReal_def, cond_apply (s_meas t (measurableSet_singleton x)),
      ENNReal.toReal_mul, ENNReal.toReal_inv, mul_comm, div_eq_mul_inv]
    congr 1
    ·
      congr 1
      congr 1
      exact Set.inter_comm _ _
  simp_rw [hP1]


-- created on 2026-10-07
