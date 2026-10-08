import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Tensor.Sum_SMul.eq.Zero.of.All_Differentiable_Prob
import Lemma.Random.Integral.eq.Sum_Sum_SMul
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
`𝔼[h(s[t]) • ∇ log π(a[t] | s[t])] = 0`
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (θ : Θ)
  (t : ℕ)
  (h : S → ℝ) :
-- imply
  ∫ ω, h (s t ω) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ
    ∂(M θ) = 0 := by
-- proof
  rw [Random.Integral.eq.Sum_Sum_SMul (M := M) h₁ θ t (fun y u => h y • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ)]
  refine Finset.sum_eq_zero fun y _ => ?_
  have h₃ : ∀ u, ((M θ).real (s t ⁻¹' {y}) * M.pol.prob θ y u) •
      (h y • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ) =
      ((M θ).real (s t ⁻¹' {y}) * h y) •
        (M.pol.prob θ y u • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ) := fun u => by
    rw [smul_smul, smul_smul]; congr 1; ring
  simp_rw [h₃]
  rw [← Finset.smul_sum, Tensor.Sum_SMul.eq.Zero.of.All_Differentiable_Prob (M := M) h₂ θ y, smul_zero]


-- created on 2026-10-06
