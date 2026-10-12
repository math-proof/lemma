import sympy.stats.policy_trajectory.gradient
import sympy.stats.cond_expectation
import Lemma.Random.All_And_LeNormExtDotPow_Id.of.All_Eq_Joint.In_Ico
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
The action value is bounded: `‖Q θ γ t x u‖ ≤ (1 - γ)⁻¹ * |R|`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (u : A) :
-- imply
  let Q (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u);
  ‖Q θ t x u‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
-- proof
  set G := (γ ^ (id : ℕ → ℕ)) @ r[t:]
  have hq : 0 ≤ (1 - γ)⁻¹ * |M.env.R| := mul_nonneg (inv_nonneg.2 (by linarith [h₀.2])) (abs_nonneg _)
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  simp only [Expectation.asRV_process]
  rw [Expectation.condEvent_eq_integral hpR.aemeasurable hfG]
  have hpre : (s t, a t) ⁻¹' {(x, u)} = s t ⁻¹' {x} ∩ a t ⁻¹' {u} := by
    ext ω
    simp [JointRandomSymbol]
  rw [hpre]
  show ‖∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}]‖ ≤ _
  have hae : ∀ᵐ ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}],
      ‖((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| :=
    cond_absolutelyContinuous.ae_le
      ((All_And_LeNormExtDotPow_Id.of.All_Eq_Joint.In_Ico (M := M) h₀ h₁ θ t).mono fun ω h => h.2)
  if hB : M θ (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) = 0 then
    rw [cond_eq_zero_of_meas_eq_zero hB]
    simpa using hq
  else
    have := cond_isProbabilityMeasure (μ := M θ) hB
    simpa using norm_integral_le_of_norm_le_const hae


-- created on 2026-10-06
-- updated on 2026-10-10
