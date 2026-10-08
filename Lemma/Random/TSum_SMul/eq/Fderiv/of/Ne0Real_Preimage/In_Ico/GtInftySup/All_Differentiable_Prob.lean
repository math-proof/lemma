import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Tensor.HasFDerivAt.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Integral.eq.MulRealPreimageSIntegral_MulEqS
import Lemma.Random.Integral_MulEqSR_Add.eq.MulRealPreimageSWRc
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


private lemma cond_r_W [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] {r : ℕ → (ℕ → ℝ × S × A) → ℝ} {s : ℕ → (ℕ → ℝ × S × A) → S} {a : ℕ → (ℕ → ℝ × S × A) → A} (h₁ : ∀ t, (· t) = (r t, s t, a t)) (M : Model Θ S A) (θ : Θ) (t k : ℕ) (x : S) (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
    ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x}] = M.W θ M.rc k x := by
  rw [Integral.eq.MulRealPreimageSIntegral_MulEqS h₁, Integral_MulEqSR_Add.eq.MulRealPreimageSWRc h₁, inv_mul_cancel_left₀ hP]

/--
on a reachable state, `∑' k, γ ^ k • ∇ 𝔼[r[t+k] | s[t] = x] = ∇ V(s[t] = x)`
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (t : ℕ)
  (x : S)
  (θ : Θ)
  (h₄ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  ∑' k, γ ^ k • fderiv ℝ (fun θ => ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x}]) θ =
    fderiv ℝ (fun θ => M.V r s θ γ t x) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₃
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {x})) θ :=
    (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₃ t x θ).continuousAt
  have hk : ∀ k, fderiv ℝ (fun θ => ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x}]) θ =
      fderiv ℝ (fun θ => M.W θ M.rc k x) θ := by
    intro k
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hc.eventually_ne h₄] with θ' h
    exact cond_r_W h₁ M θ' t k x h
  simp_rw [hk]
  rw [Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃ t x θ h₄, (Tensor.HasFDerivAt.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₂ h₃ h₀ x θ).fderiv]


-- created on 2026-10-06
