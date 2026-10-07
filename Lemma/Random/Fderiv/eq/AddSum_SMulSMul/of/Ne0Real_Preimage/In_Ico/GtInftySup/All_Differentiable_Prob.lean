import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Tensor.Fderiv.eq.AddSum_SMulSMul.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Tensor.Fderiv_Prob.eq.Zero.of.EqProb_0
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


private lemma Q_eq_Qc [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A] (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (t : ℕ) (x : S) (u : A) (hP : (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u ≠ 0) :
    M.Q θ γ t x u = M.Qc θ γ x u := by
  exact Q_eq M θ hγ t x u hP

/--
policy-gradient recursion for the model value functions on a reachable state
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₁ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (h₂ : γ ∈ Set.Ico 0 1)
  (t : ℕ)
  (x : S)
  (θ : Θ)
  (h₃ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  fderiv ℝ (fun θ' => M.V θ' γ t x) θ =
    ∑ u, M.Q θ γ t x u • fderiv ℝ (fun θ' => M.pol.prob θ' x u) θ +
    γ • ∑ y, M.P1 θ x y • fderiv ℝ (fun θ' => M.V θ' γ (t + 1) y) θ := by
-- proof
  obtain ⟨Cp, hCp⟩ := id h₁
  have hC : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ Cp := fun θ x u => by
    simpa [gradient, LinearIsometryEquiv.norm_map] using hCp ⟨(θ, x, u), rfl⟩
  rw [Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ t x θ h₃, Tensor.Fderiv.eq.AddSum_SMulSMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ x θ]
  congr 1
  · refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : M.pol.prob θ x u = 0
    · rw [Tensor.Fderiv_Prob.eq.Zero.of.EqProb_0 (M := M) θ x u hu, smul_zero, smul_zero]
    · rw [Q_eq_Qc M θ h₂ t x u (mul_ne_zero h₃ hu)]
  · congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : M.P1 θ x y = 0
    · rw [hy, zero_smul, zero_smul]
    · obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
      rw [Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ (t + 1) y θ (reach M θ t x u y h₃ hu)]


-- created on 2026-10-06
