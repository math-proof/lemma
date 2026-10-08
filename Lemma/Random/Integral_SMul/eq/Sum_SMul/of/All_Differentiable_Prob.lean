import sympy.stats.policy_trajectory.gradient
import sympy.Basic
import Lemma.Tensor.SMul.eq.Fderiv.of.All_Differentiable_Prob
import Lemma.Random.Integral.eq.Sum_Sum_SMul
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model


/--
`𝔼[g(s[t], a[t]) • ∇ log π(a[t] | s[t])] = ∑ y, Pr(s[t] = y) • ∑ u, g y u • ∇ π(u | y)`
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (θ : Θ)
  (t : ℕ)
  (g : S → A → ℝ) :
-- imply
  ∫ ω, g (state t ω) (action t ω) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (state t ω) (action t ω))) θ
    ∂(M θ) =
    ∑ y, (M θ).real (state t ⁻¹' {y}) •
    ∑ u, g y u • fderiv ℝ (fun θ' => M.pol.prob θ' y u) θ := by
-- proof
  rw [Random.Integral.eq.Sum_Sum_SMul (M := M) θ t (fun y u => g y u • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Tensor.SMul.eq.Fderiv.of.All_Differentiable_Prob (M := M) h₀ θ y u, smul_smul, smul_smul, smul_smul]
  congr 1
  ring


-- created on 2026-10-06
