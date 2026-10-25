import Lemma.Random.GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico
import Macro.Algebra.BigOperators.Summations
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.ProbCond.eq.Div.of.SinglePSpace
import Lemma.Random.SinglePSpace.of.Measurable.Measurable
import Lemma.Random.RealPreimageSPreimageS_Add_1.eq.P1.of.Ne0Real_Preimage
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Topology Random
open scoped ENNReal.ToRealCoe


/--
Policy-gradient recursion with a discrete (finite) state space and a discrete (finite) action space:
∇V(s[t] = s.bvar[t]) = ∑ a.bvar[t], Q(s.bvar[t], a.bvar[t]) • ∇ℙ(a[t] = a.bvar[t] | s[t] = s.bvar[t]) + γ • ∑ s.bvar[t+1], ℙ(s[t+1] = s.bvar[t+1] | s[t] = s.bvar[t]) • ∇V(s[t+1] = s.bvar[t+1]),
the gradient of the Bellman equations of extract_QVA on a reachable state s.bvar[t] (h₆ : ℙ(s[t] = s.bvar[t]) ≠ 0).
It is the discrete/discrete case next to the continuous-state/discrete-action
`Random.GradVk.eq.Add_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Differentiable_Prob.In_Ico`,
the continuous/continuous
`Random.GradVkd.eq.AddIntegral_SMul_Integral_SMul.of.All_EqWithDensity.All_Ge_0.All_Measurable.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico`
and the discrete-state/continuous-action
`Random.GradVkd.eq.AddIntegral_SMul_Sum_SMul.of.All_EqReal.All_Measurable_Prob.GtInftySup.All_Integrable.All_LeNormGrad.All_Differentiable_Prob.In_Ico`
versions. The reference measures of `S` and `A` are counting (`CountableMeasure`), so the conditional probabilities are
elementary: ℙ(a[t] = u | s[t] = x) = π_θ(u | x) on reachable states and ℙ(s[t+1] = y | s[t] = x) = P1 θ x y.
h₂, h₃: Q, V are the action and state values, i.e. the conditional expectations of the discounted return
given `s[t] = x, a[t] = u` (resp. `s[t] = x`), as functions of the weights θ;
h₄, h₅: θ ↦ π_θ(u | x) is differentiable with a bounded gradient.
The proof identifies Q and V with the local action and state values, then applies
`Random.GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
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
  (h₂ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q θ t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₃ : ∀ θ t («s.bvar» : ℕ → S), V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₅ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (h₆ : (M θ).real (s t ⁻¹' {«s.bvar» t}) ≠ 0)
  (hP : ∀ θ y, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {y}) ≠ 0)
  (hπ : ∀ θ u, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {«s.bvar» t}) * M.policy.prob θ («s.bvar» t) u ≠ 0) :
-- imply
  have hs : ∀ t, Measurable (s t) := Random.Measurable.of.All_Eq.snd.fst h₁
  have ha : ∀ t, Measurable (a t) := Random.Measurable.of.All_Eq.snd.snd h₁
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.Measurable.Measurable (ha t) (hs t)
  have : ∀ θ t, SinglePSpace (M θ) (s (t + 1), s t) := fun _ t =>
    SinglePSpace.of.Measurable.Measurable (hs (t + 1)) (hs t)
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
  intro hs ha hSPA hSPS
  let Qloc (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
  let Vloc (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)
  have hQ : Q = Qloc := funext fun θ => funext fun t => funext fun x => funext fun u =>
    h₂ θ t (fun _ ↦ x) (fun _ ↦ u)
  have hV : V = Vloc := funext fun θ => funext fun t => funext fun x =>
    h₃ θ t (fun _ ↦ x)
  subst hQ hV
  classical
  beta_reduce
  set x := «s.bvar» t
  have hπ_eq : ∀ u, ∇[θ] (ℙ[M θ]((a t) = u | (s t) = x) : ℝ) = ∇[θ] M.policy.prob θ x u := by
    intro u
    refine Filter.EventuallyEq.gradient_eq ?_
    filter_upwards [(Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₄ h₅ t x θ).continuousAt.eventually_ne h₆] with θ' h
    erw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ (hSPA θ' t) h, ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
  simp only [s, a] at hπ_eq
  simp_rw [hπ_eq]
  rw [GradV.eq.AddSum_SMulSMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.In_Ico h₀ h₁ h₄ h₅ h₆ hP hπ]
  have hP1 : ∀ y, (ℙ[M θ]((s (t + 1)) = y | (s t) = x) : ℝ) = M.P1 θ x y := by
    intro y
    rw [ProbCond.eq.Div.of.SinglePSpace inferInstance (π := M θ) (x := s (t + 1)) (y := s t) y x,
      ENNReal.toReal_div, ← RealPreimageSPreimageS_Add_1.eq.P1.of.Ne0Real_Preimage (M := M) θ t x y h₁ h₆,
      measureReal_def]
    erw [cond_apply (hs t (measurableSet_singleton x))]
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, mul_comm, div_eq_mul_inv]
    congr 3
    apply Set.inter_comm
  simp only [s] at hP1
  simp_rw [hP1]
  simp only [Qloc, Vloc]


-- created on 2023-03-30
-- updated on 2026-10-23
