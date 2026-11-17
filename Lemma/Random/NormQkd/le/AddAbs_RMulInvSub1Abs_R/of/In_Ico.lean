import Theorem.Probability.CondExpectation
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity
import Theorem.Probability.JointRv.AsRV
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
For `γ ∈ [0, 1)` the action value with a density policy is bounded on atoms of positive mass:
`‖Q0 θ γ x u‖ ≤ |R| + γ * (1 - γ)⁻¹ * |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSingletonClass 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {γ : ℝ}
-- given
  (h : γ ∈ Set.Ico 0 1)
  (θ : Θ)
  (sₜ : 𝒮)
  (aₜ : 𝒜)
  (hpos : (M.traj θ) ((fun ω => (ω 0).2.1) ⁻¹' {sₜ} ∩ (fun ω => (ω 0).2.2) ⁻¹' {aₜ}) ≠ 0) :
-- imply
  ‖M.Q0 θ γ sₜ aₜ‖ ≤ |M.R| + γ * ((1 - γ)⁻¹ * |M.R|) := by
-- proof
  let r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun t ω => (ω t).1
  let s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω => (ω t).2.1
  let a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω => (ω t).2.2
  have h₁ : ∀ t, (· t) = (r t, s t, a t) := fun t => funext fun ω => rfl
  have hq : 0 ≤ (1 - γ)⁻¹ * |M.R| :=
    mul_nonneg (inv_nonneg.2 (by linarith [h.2])) (abs_nonneg _)
  unfold Model.Q0 Model.Q
  simp only [Expectation.asRV_process]
  have hpR : Measurable (fun ω t ↦ r t ω) :=
    Measurable.of_eval fun t => measurable_fst.comp (measurable_pi_apply t)
  have hy : Measurable (s 0, a 0) :=
    ((measurable_pi_apply 0).snd.fst).prodMk ((measurable_pi_apply 0).snd.snd)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) ⬝ᵥ integ[0:]) := by
    unfold Dot.dot Function.getSliceFrom
    refine Measurable.tsum fun k => ?_
    have hm : Measurable (fun integ : ℕ → ℝ => integ (0 + k)) := measurable_pi_apply (0 + k)
    simpa using hm.const_mul ((γ ^ (id : ℕ → ℕ)) k)
  have hpre : (s 0, a 0) ⁻¹' {(sₜ, aₜ)} =
      (fun ω => (ω 0).2.1) ⁻¹' {sₜ} ∩ (fun ω => (ω 0).2.2) ⁻¹' {aₜ} := by
    ext ω
    simp [JointRandomSymbol, s, a, Set.mem_preimage, Set.mem_inter_iff,
      Set.mem_singleton_iff, Prod.ext_iff]
  have hmap : (M.traj θ).map (s 0, a 0) {(sₜ, aₜ)} ≠ 0 := by
    rwa [Measure.map_apply hy (measurableSet_singleton (sₜ, aₜ)), hpre]
  rw [Expectation.condEval_eq_integral hpR hy hfG hmap]
  show ‖∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[0:]) ω ∂(M.traj θ)[|(s 0, a 0) ⁻¹' {(sₜ, aₜ)}]‖ ≤ _
  have hG : ∀ᵐ ω ∂(M.traj θ), ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[0:]) ω‖ ≤ (1 - γ)⁻¹ * |M.R| := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint.All_EqWithDensity h₁ (M := M) θ] with ω hr
    unfold instDotNatArrowProcess Dot.dot Function.getSliceFrom
    simp only [zero_add]
    have hb : ∀ k, ‖γ ^ k * r k ω‖ ≤ γ ^ k * |M.R| := fun k => by
      rw [norm_mul, norm_pow, Real.norm_of_nonneg h.1]
      apply mul_le_mul_of_nonneg_left (hr k) (pow_nonneg h.1 k)
    apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h.1 h.2).mul_right _) hb
  have hae : ∀ᵐ ω ∂(M.traj θ)[|(s 0, a 0) ⁻¹' {(sₜ, aₜ)}],
      ‖((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[0:]) ω‖ ≤ (1 - γ)⁻¹ * |M.R| :=
    cond_absolutelyContinuous.ae_le hG
  have hle : ‖∫ ω, ((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r[0:]) ω ∂(M.traj θ)[|(s 0, a 0) ⁻¹' {(sₜ, aₜ)}]‖ ≤
      (1 - γ)⁻¹ * |M.R| := by
    have : (M.traj θ) ((s 0, a 0) ⁻¹' {(sₜ, aₜ)}) ≠ 0 := by
      rwa [hpre]
    have := cond_isProbabilityMeasure (μ := M.traj θ) this
    simpa using norm_integral_le_of_norm_le_const hae
  have hid : (1 - γ)⁻¹ * |M.R| = |M.R| + γ * ((1 - γ)⁻¹ * |M.R|) := by
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
-- updated on 2026-11-17