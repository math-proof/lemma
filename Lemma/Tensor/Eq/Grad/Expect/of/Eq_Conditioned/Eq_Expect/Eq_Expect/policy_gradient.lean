import Lemma.Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct
import sympy.stats.cond_expectation
import sympy.core.power
import sympy.vector.Basic
import sympy.vector.operators
import Mathlib.Analysis.Calculus.Gradient.Basic
import sympy.concrete.sup
import Lemma.Random.RealPreimageSPreimageS_Add.eq.Pn.of.Ne0Real_Preimage
import Lemma.Random.RealPreimageS0.eq.Real
import Lemma.Random.RealPreimageS.eq.Sum_MulRealPn
import Lemma.Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Integral.eq.Sum_SMul
import Lemma.Random.Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob
import Lemma.Random.TSum_SMul.eq.Sum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Integrable_Fun
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


/--
Finite-horizon policy gradient: for every `n`,
`γ ** Stack[t](t) @ ∇𝔼[r] = 𝔼[∑ t < n, γ ^ t * Q(s[t], a[t]) • ∇ log π(a[t] | s[t])] + γ ^ n • 𝔼[∇V(s[n])]`,
where `γ ** Stack[t](t) @ ∇𝔼[r]` is `∑' t, γ ^ t • ∇_θ 𝔼[r[t]]`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
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
  (n : ℕ) :
-- imply
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
    ∫ ω, ∑ t ∈ Finset.range n, (γ ^ t * Q θ t (s t ω) (a t ω)) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
      γ ^ n • ∫ ω, fderiv ℝ (fun θ' => V θ' n (s n ω)) θ ∂(M θ) := by
-- proof
  have h₄n := h₄
  simp only [gradient, LinearIsometryEquiv.norm_map] at h₄
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
  have h₇ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  classical
  beta_reduce
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
  have h₈ : ∀ x, M.env.init.real {x} • fderiv ℝ (fun θ => M.Vc θ γ x) θ =
      M.env.init.real {x} • (∑ t ∈ Finset.range n, γ ^ t • ∑ y, M.Pn θ t x y •
          ∑ u, M.Q θ γ t y u • fderiv ℝ (fun θ => M.pol.prob θ y u) θ +
        γ ^ n • ∑ y, M.Pn θ n x y • fderiv ℝ (fun θ => M.V θ γ n y) θ) := by
    intro x
    by_cases hx : M.env.init.real {x} = 0
    · rw [hx, zero_smul, zero_smul]
    have hP : (M θ).real (s 0 ⁻¹' {x}) ≠ 0 := by rwa [Random.RealPreimageS0.eq.Real]
    have hg := Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct
      h₀ hS hA (Q := fun θ => M.Q θ γ) (V := fun θ => M.V θ γ) hQ_expect hV_expect
      h₃ h₄n hP n
    have h' : ∀ t y, ((M θ)[|s 0 ⁻¹' {x}]).real (s t ⁻¹' {y}) = M.Pn θ t x y := fun t y => by
      have h'' := Random.RealPreimageSPreimageS_Add.eq.Pn.of.Ne0Real_Preimage (M := M) θ 0 t x y hP
      rwa [zero_add] at h''
    simp_rw [h'] at hg
    have h : fderiv ℝ (fun θ => M.V θ γ 0 x) θ =
        ∑ t ∈ Finset.range n, γ ^ t • ∑ y, M.Pn θ t x y •
            ∑ u, M.Q θ γ t y u • fderiv ℝ (fun θ => M.pol.prob θ y u) θ +
          γ ^ n • ∑ y, M.Pn θ n x y • fderiv ℝ (fun θ => M.V θ γ n y) θ := by
      apply (InnerProductSpace.toDual ℝ Θ).symm.injective
      simpa [gradient, map_add, map_smul, map_sum] using hg
    rw [← Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₃ h₄n h₀ 0 x θ hP, h]
  have h₉ : ∀ t, ∫ ω, (γ ^ t * M.Q θ γ t (s t ω) (a t ω)) •
      fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
      ∑ y, (M θ).real (s t ⁻¹' {y}) •
        ∑ u, (γ ^ t * M.Q θ γ t y u) • fderiv ℝ (fun θ' => M.pol.prob θ' y u) θ :=
    fun t => Random.Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob (M := M) h₃ θ t (fun y u => γ ^ t * M.Q θ γ t y u)
  have h₁₀ : ∫ ω, fderiv ℝ (fun θ' => M.V θ' γ n (s n ω)) θ ∂(M θ) =
      ∑ y, (M θ).real (s n ⁻¹' {y}) • fderiv ℝ (fun θ' => M.V θ' γ n y) θ :=
    Random.Integral.eq.Sum_SMul (M := M) θ n (fun y => fderiv ℝ (fun θ' => M.V θ' γ n y) θ)
  rw [Random.TSum_SMul.eq.Sum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₃ h₄n h₀ θ, Finset.sum_congr rfl fun x _ => h₈ x,
    integral_finsetSum _ fun t _ => Random.Integrable_Fun (M := M) θ t
      (fun y u => (γ ^ t * M.Q θ γ t y u) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ)]
  simp_rw [h₉, h₁₀, Random.RealPreimageS.eq.Sum_MulRealPn (M := M) θ]
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul,
    Finset.sum_mul]
  congr 1
  · conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => ?_
    congr 1
    ring
  · conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    congr 1
    ring


-- created on 2023-04-04
-- updated on 2026-10-05
