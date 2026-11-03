import Theorem.Probability.CondExpectation
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.DensityModel Random


/--
For `γ ∈ [0, 1)` the action value with a density policy is bounded:
`‖Q0 θ γ x u‖ ≤ |R| + γ * (1 - γ)⁻¹ * |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {γ : ℝ}
-- given
  (h : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (x : S)
  (u : A) :
-- imply
  ‖M.Q0 θ γ x u‖ ≤ |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) := by
-- proof
  let r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω => (ω t).1
  let s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω => (ω t).2.1
  let a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω => (ω t).2.2
  have h₁ : ∀ t, (· t) = (r t, s t, a t) := fun t => funext fun ω => rfl
  have hq : 0 ≤ (1 - γ)⁻¹ * |M.env.R| :=
    mul_nonneg (inv_nonneg.2 (by linarith [h.2])) (abs_nonneg _)
  unfold DensityModel.Q0 DensityModel.Q
  simp only [Expectation.asRV_process]
  have hpR : Measurable (fun ω t ↦ r t ω) :=
    Measurable.of_eval fun t => measurable_fst.comp (measurable_pi_apply t)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[0:]) := by
    unfold Dot.dot Function.getSliceFrom
    refine Measurable.tsum fun k => ?_
    have hm : Measurable (fun integ : ℕ → ℝ => integ (0 + k)) := measurable_pi_apply (0 + k)
    simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
  rw [Expectation.condEvent_eq_integral hpR.aemeasurable hfG]
  show ‖∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[0:]) ω ∂(M θ)[|(s 0, a 0) ⁻¹' {(x, u)}]‖ ≤ _
  have hG : ∀ᵐ ω ∂(M θ), ‖((γ ^ (id : ℕ → ℕ)) @ r[0:]) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ (M := M) θ] with ω hr
    unfold instDotNatArrowProcess Dot.dot Function.getSliceFrom
    simp only [zero_add]
    have hb : ∀ k, ‖γ ^ k * r k ω‖ ≤ γ ^ k * |M.env.R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h.1]
      apply mul_le_mul_of_nonneg_left (hr k) (pow_nonneg h.1 k)
    apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h.1 h.2).mul_right _) hb
  have hae : ∀ᵐ ω ∂(M θ)[|(s 0, a 0) ⁻¹' {(x, u)}],
      ‖((γ ^ (id : ℕ → ℕ)) @ r[0:]) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    cond_absolutelyContinuous.ae_le hG
  have hle : ‖∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[0:]) ω ∂(M θ)[|(s 0, a 0) ⁻¹' {(x, u)}]‖ ≤
      (1 - γ)⁻¹ * |M.env.R| := by
    if hB : (M θ) ((s 0, a 0) ⁻¹' {(x, u)}) = 0 then
      rw [cond_eq_zero_of_meas_eq_zero hB]
      simpa using hq
    else
      have := cond_isProbabilityMeasure (μ := M θ) hB
      simpa using norm_integral_le_of_norm_le_const hae
  have hid : (1 - γ)⁻¹ * |M.env.R| = |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) := by
    have hne : (1 - γ) ≠ 0 := sub_ne_zero.2 (ne_of_lt h.2).symm
    have hinv : (1 - γ)⁻¹ = 1 + γ * (1 - γ)⁻¹ := by
      apply mul_left_cancel₀ hne
      rw [mul_inv_cancel₀ hne, mul_add, mul_one]
      have : (1 - γ) * (γ * (1 - γ)⁻¹) = γ := by
        rw [mul_left_comm, mul_inv_cancel₀ hne, mul_one]
      rw [this, sub_add_cancel]
    conv_lhs => rw [hinv]
    ring
  exact hle.trans (le_of_eq hid)


-- created on 2026-11-02
-- updated on 2026-11-02
