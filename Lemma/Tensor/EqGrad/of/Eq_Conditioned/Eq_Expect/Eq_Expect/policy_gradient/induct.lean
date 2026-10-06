import Lemma.Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.recursion.discrete
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
import Lemma.Random.RealPreimageSPreimageS_Add.eq.Pn.of.NeRealPreimageS_0
import Lemma.Random.RealPreimageSPreimageS_Add_1.eq.P1.of.NeRealPreimageS_0
import Lemma.Tensor.Differentiable_RealPreimageS.of.IsFinite.All_Differentiable_Prob
import Lemma.Random.RealPreimageS.ne.Zero.of.NePn_0.NeRealPreimageS0_0
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology


/--
Unrolled policy-gradient recursion: for a reachable initial state x (h₅) and every 
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
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₁ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q θ t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₂ : ∀ θ t («s.bvar» : ℕ → S), V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₃ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₄ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₅ : (M θ).real (s 0 ⁻¹' {x}) ≠ 0)
  (n : ℕ) :
-- imply
  ∇[θ] V θ 0 x =
    ∑ t ∈ Finset.range n, γ ^ t • ∑ y, ((M θ)[|s 0 ⁻¹' {x}]).real (s t ⁻¹' {y}) •
        ∑ u, Q θ t y u • ∇[θ] M.pol.prob θ y u +
      γ ^ n • ∑ y, ((M θ)[|s 0 ⁻¹' {x}]).real (s n ⁻¹' {y}) • ∇[θ] V θ n y := by
-- proof
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
  obtain ⟨C, hC⟩ := id h₄
  have h₇ : ∀ θ x u, ‖∇[θ] M.pol.prob θ x u‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  classical
  beta_reduce
  have h₈ : ∀ t y, ((M θ)[|s 0 ⁻¹' {x}]).real (s t ⁻¹' {y}) = M.Pn θ t x y := fun t y => by
    have h := Random.RealPreimageSPreimageS_Add.eq.Pn.of.NeRealPreimageS_0 (M := M) θ 0 t x y h₅
    rwa [zero_add] at h
  simp_rw [h₈]
  have hQ_expect : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A),
      M.Q θ γ t («s.bvar» t) («a.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t) := by
    intro θ t sb ab
    symm
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    have hpre : JointRandomSymbol (s (S := S) (A := A) t) (a (S := S) (A := A) t) ⁻¹' {(sb t, ab t)} =
        s t ⁻¹' {sb t} ∩ a t ⁻¹' {ab t} := by
      ext ω; simp [JointRandomSymbol, Prod.ext_iff]
    rw [hpre]
    exact Model.integral_G_cond M θ h₀ _ t
  have hV_expect : ∀ θ t («s.bvar» : ℕ → S),
      M.V θ γ t («s.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t) := by
    intro θ t sb
    symm
    rw [M.V_eq_integral θ γ t (sb t)]
    simp only [Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable (hfG t)]
    rfl
  induction n with
  | zero => simp [Random.Pn0.eq.Eq]
  | succ n ih =>
    have h₉ : ∀ y, M.Pn θ n x y • ∇[θ] M.V θ γ n y =
        M.Pn θ n x y • (∑ u, M.Q θ γ n y u • ∇[θ] M.pol.prob θ y u +
          γ • ∑ z, M.P1 θ y z • ∇[θ] M.V θ γ (n + 1) z) := by
      intro y
      by_cases hy : M.Pn θ n x y = 0
      · rw [hy, zero_smul, zero_smul]
      have hP := Random.RealPreimageS.ne.Zero.of.NePn_0.NeRealPreimageS0_0 (M := M) θ n x y h₅ hy
      have h := Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.recursion.discrete
        («s.bvar» := fun _ ↦ y)
        h₀ hS hA (Q := fun θ => M.Q θ γ) (V := fun θ => M.V θ γ) hQ_expect hV_expect h₃ h₄ hP
      have hSingle : ∀ θ t, SinglePSpace (M θ) (a (S := S) (A := A) t, s (S := S) (A := A) t) := fun _ t =>
        Random.SinglePSpace.of.EqMeasureCount.Measurable ((a_meas t).prodMk (s_meas t)) (by
          show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
          rw [hA, hS, Measure.Count.eq.ProdCountS])
      have h₇f : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => by
        simpa [gradient, LinearIsometryEquiv.norm_map] using h₇ θ x u
      have hπ : ∀ u, ∇[θ] ℙ[M θ]((a n) = u | (s n) = y).toReal = ∇[θ] M.pol.prob θ y u := by
        intro u
        have hc : ContinuousAt (fun θ' => (M θ').real (s n ⁻¹' {y})) θ :=
          (Tensor.Differentiable_RealPreimageS.of.IsFinite.All_Differentiable_Prob (M := M) h₃ h₇f n y θ).continuousAt
        refine Filter.EventuallyEq.gradient_eq ?_
        filter_upwards [hc.eventually_ne hP] with θ' h
        beta_reduce
        rw [Random.ProbCond.eq.OfRealPol.of.Ne_0 hS hA (hSingle θ' n) h,
          ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
      simp_rw [hπ] at h
      rw [h]
      have hSs : ∀ θ t, SinglePSpace (M θ) (s (S := S) (A := A) (t + 1), s (S := S) (A := A) t) :=
        fun _ t => Random.SinglePSpace.of.EqMeasureCount.EqMeasureCount.Measurable.Measurable
          (s_meas (t + 1)) (s_meas t) hS hS
      have hP1 : ∀ z, ℙ[M θ]((s (n + 1)) = z | (s n) = y).toReal = M.P1 θ y z := by
        intro z
        have hDiv := Random.ProbCond.eq.Div.of.Eq_Count.Eq_Count (π := M θ)
          (x := s (S := S) (A := A) (n + 1)) (y := s (S := S) (A := A) n) hS hS z y
        rw [hDiv, ENNReal.toReal_div, ← Random.RealPreimageSPreimageS_Add_1.eq.P1.of.NeRealPreimageS_0 (M := M) θ n y z hP]
        rw [measureReal_def, cond_apply (s_meas n (measurableSet_singleton y)),
          ENNReal.toReal_mul, ENNReal.toReal_inv, mul_comm, div_eq_mul_inv]
        congr 1
        · congr 1
          congr 1
          exact Set.inter_comm _ _
      simp_rw [hP1]
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    rw [Finset.sum_congr rfl fun y _ => h₉ y]
    simp_rw [smul_add, Finset.sum_add_distrib, smul_add]
    congr 1
    simp_rw [Random.PnAdd_1.eq.Sum_MulPnP1, Finset.sum_smul, Finset.smul_sum, smul_smul]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    ring


-- created on 2023-03-30
-- updated on 2026-10-06
