import Lemma.Random.Grad.eq.Add_SMul_Sum_SMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.All_Eq_Expect.All_Eq_Expect.EqMeasureCount.EqMeasureCount.In_Ico
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import Lemma.Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
import Lemma.Measure.Count.eq.ProdCountS
import sympy.stats.cond_expectation
import sympy.core.power
import sympy.vector.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Random.Pn0.eq.Eq
import Lemma.Random.PnAdd_1.eq.Sum_MulPnP1
import Lemma.Random.RealPreimageSPreimageS_Add.eq.Pn.of.Ne0Real_Preimage
import Lemma.Random.RealPreimageSPreimageS_Add_1.eq.P1.of.Ne0Real_Preimage
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.RealPreimageS.ne.Zero.of.NePn_0.Ne0Real_Preimage
import sympy.core.numbers
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Measurable_A
import Lemma.Random.Measurable_S
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure
open scoped ENNReal.ToRealCoe


/--
Unrolled policy-gradient recursion: for a reachable initial state x (h₆) and every 
,
∇V(s[0] = x) = ∑ t < n, γ ^ t • ∑ y, Pr(s[t] = y | s[0] = x) • ∑ u, Q(y, u) • ∇π(u | y)
  + γ ^ n • ∑ y, Pr(s[n] = y | s[0] = x) • ∇V(s[n] = y).
The sympy path integral ∫ ∏ Pr(s[t+1] | s[t]) over s[1:t+1] is written as the 	-step
conditional probability Pr(s[t] = y | s[0] = x) (Chapman–Kolmogorov).
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {x : S}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₂ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q θ t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₃ : ∀ θ t («s.bvar» : ℕ → S), V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₅ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₆ : (M θ).real (s 0 ⁻¹' {x}) ≠ 0)
  (n : ℕ) :
-- imply
  ∇[θ] V θ 0 x =
    ∑ t ∈ Finset.range n, γ ^ t • ∑ y, ((M θ)[|s 0 ⁻¹' {x}]).real (s t ⁻¹' {y}) •
        ∑ u, Q θ t y u • ∇[θ] M.pol.prob θ y u +
      γ ^ n • ∑ y, ((M θ)[|s 0 ⁻¹' {x}]).real (s n ⁻¹' {y}) • ∇[θ] V θ n y := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have hr : ∀ t, Measurable (r t) := Model.r_meas' h₁
  have hpR : Measurable (fun ω t ↦ r t ω) := measurable_pi_lambda _ hr
  have hfG : ∀ t, Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) := fun t =>
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hQ : Q = fun θ => M.Q r s a θ γ := funext fun θ => funext fun t => funext fun x => funext fun u => by
    rw [h₂ θ t (fun _ ↦ x) (fun _ ↦ u)]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    have hpre : JointRandomSymbol (s t) (a t) ⁻¹' {(x, u)} =
        s t ⁻¹' {x} ∩ a t ⁻¹' {u} := by
      ext ω; simp [JointRandomSymbol, Prod.ext_iff]
    rw [hpre]
    exact Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ h₁ θ _ t
  have hV : V = fun θ => M.V r s θ γ := funext fun θ => funext fun t => funext fun x => by
    rw [h₃ θ t (fun _ ↦ x), M.V_eq_integral r s θ γ t x]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    rfl
  subst hQ hV
  classical
  beta_reduce
  have h₈ : ∀ t y, ((M θ)[|s 0 ⁻¹' {x}]).real (s t ⁻¹' {y}) = M.Pn θ t x y := fun t y => by
    have h := RealPreimageSPreimageS_Add.eq.Pn.of.Ne0Real_Preimage (M := M) h₁ θ 0 t x y h₆
    rwa [zero_add] at h
  simp_rw [h₈]
  have hQ_expect : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A),
      M.Q r s a θ γ t («s.bvar» t) («a.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t) := by
    intro θ t sb ab
    symm
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    have hpre : JointRandomSymbol (s t) (a t) ⁻¹' {(sb t, ab t)} =
        s t ⁻¹' {sb t} ∩ a t ⁻¹' {ab t} := by
      ext ω; simp [JointRandomSymbol, Prod.ext_iff]
    rw [hpre]
    exact Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ h₁ θ _ t
  have hV_expect : ∀ θ t («s.bvar» : ℕ → S),
      M.V r s θ γ t («s.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t) := by
    intro θ t sb
    symm
    rw [M.V_eq_integral r s θ γ t (sb t)]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    rfl
  induction n with
  | zero => simp [Pn0.eq.Eq]
  | succ n ih =>
    have h₉ : ∀ y, M.Pn θ n x y • ∇[θ] M.V r s θ γ n y =
        M.Pn θ n x y • (∑ u, M.Q r s a θ γ n y u • ∇[θ] M.pol.prob θ y u +
          γ • ∑ z, M.P1 θ y z • ∇[θ] M.V r s θ γ (n + 1) z) := by
      intro y
      if hy : M.Pn θ n x y = 0 then
        rw [hy, zero_smul, zero_smul]
      else
        have hP := RealPreimageS.ne.Zero.of.NePn_0.Ne0Real_Preimage (M := M) h₁ θ n x y h₆ hy
        have h := Grad.eq.Add_SMul_Sum_SMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.All_Eq_Expect.All_Eq_Expect.EqMeasureCount.EqMeasureCount.In_Ico
          («s.bvar» := fun _ ↦ y)
          h₀ h₁ hS hA (Q := fun θ => M.Q r s a θ γ) (V := fun θ => M.V r s θ γ) hQ_expect hV_expect h₄ h₅ hP
        have hμAS : ReferenceMeasure.measure (α := A × S) = Measure.count := by
          show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
          rw [hA, hS, Count.eq.ProdCountS]
        have hSingle : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
          SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable_A h₁ t).prodMk (Random.Measurable_S h₁ t)) hμAS
        have hπ : ∀ u, ∇[θ] (ℙ[M θ]((a n) = u | (s n) = y) : ℝ) = ∇[θ] M.pol.prob θ y u := by
          intro u
          have hc : ContinuousAt (fun θ' => (M θ').real (s n ⁻¹' {y})) θ :=
            (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₄ h₅ n y θ).continuousAt
          refine Filter.EventuallyEq.gradient_eq ?_
          filter_upwards [hc.eventually_ne hP] with θ' h
          beta_reduce
          rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ hS hA (hSingle θ' n) h,
            ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
        simp_rw [hπ] at h
        rw [h]
        have hSs : ∀ θ t, SinglePSpace (M θ) (s (t + 1), s t) :=
          fun _ t => SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
            (Random.Measurable_S h₁ (t + 1)) (Random.Measurable_S h₁ t) hS hS
        have hP1 : ∀ z, (ℙ[M θ]((s (n + 1)) = z | (s n) = y) : ℝ) = M.P1 θ y z := by
          intro z
          have hDiv := ProbCond.eq.Div.of.Eq_Count.Eq_Count (π := M θ)
            (x := s (n + 1)) (y := s n) hS hS z y
          rw [hDiv, ENNReal.toReal_div, ← RealPreimageSPreimageS_Add_1.eq.P1.of.Ne0Real_Preimage (M := M) h₁ θ n y z hP]
          rw [measureReal_def, cond_apply (Random.Measurable_S h₁ n (measurableSet_singleton y)),
            ENNReal.toReal_mul, ENNReal.toReal_inv, mul_comm, div_eq_mul_inv]
          congr 1
          ·
            congr 1
            congr 1
            exact Set.inter_comm _ _
        simp_rw [hP1]
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    rw [Finset.sum_congr rfl fun y _ => h₉ y]
    simp_rw [smul_add, Finset.sum_add_distrib, smul_add]
    congr 1
    simp_rw [PnAdd_1.eq.Sum_MulPnP1, Finset.sum_smul, Finset.smul_sum, smul_smul]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    ring


-- created on 2023-03-30
-- updated on 2026-10-07
