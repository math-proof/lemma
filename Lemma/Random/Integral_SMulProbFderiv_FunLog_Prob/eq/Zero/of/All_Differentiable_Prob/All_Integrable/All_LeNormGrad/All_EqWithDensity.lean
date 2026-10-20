import Mathlib.Analysis.Calculus.ParametricIntegral
import Lemma.Random.EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb.All_EqWithDensity
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
open MeasureTheory ProbabilityTheory Topology PolicyGradient Random Real


/--
Zero expected score for a density policy:
`∫ u, π_θ(u | x) • ∇ log π_θ(u | x) du = 0` (no positivity needed).
Continuous-action counterpart of
`Random.SumSMulProbFderiv_FunLog_Prob.eq.Zero.of.All_AllDifferentiable_FunProbPol`:
rewrite via `π • ∇ log π = ∇π`, then differentiate under the integral
`∫ π = 1` to get `∫ ∇π = ∇1 = 0`, using a dominating integrable bound on `‖∇π‖`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {g : S → A → ℝ}
-- given
  (h₀ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₁ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.policy.prob θ x u) θ‖ ≤ g x u)
  (h₂ : ∀ x, Integrable (g x) ReferenceMeasure.measure)
  (θ : Θ)
  (x : S) :
-- imply
  ∫ u, M.policy.prob θ x u • fderiv ℝ (fun θ' => Real.log (M.policy.prob θ' x u)) θ
    ∂ReferenceMeasure.measure = 0 := by
-- proof
  have hSf : StronglyMeasurable (fun u => fderiv ℝ (fun θ => M.policy.prob θ x u) θ) :=
    StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
      (fun θ' => (M.policy.measurable_prob θ').comp measurable_prodMk_left)
      (fun u => (h₀ x u) θ)
  have hIπ : Integrable (M.policy.prob θ x) ReferenceMeasure.measure :=
    Integrable.of_integral_ne_zero (by simp [M.policy.integral_eq_one θ x])
  have hF : HasFDerivAt (fun θ' => ∫ u, M.policy.prob θ' x u ∂ReferenceMeasure.measure)
      (∫ u, fderiv ℝ (fun θ' => M.policy.prob θ' x u) θ ∂ReferenceMeasure.measure) θ :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun θ' u => M.policy.prob θ' x u)
      (F' := fun θ' u => fderiv ℝ (fun θ'' => M.policy.prob θ'' x u) θ')
      (s := Set.univ) (bound := g x) Filter.univ_mem
      (Filter.Eventually.of_forall fun θ' =>
        ((M.policy.measurable_prob θ').comp measurable_prodMk_left).aestronglyMeasurable)
      hIπ
      hSf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u θ' _ => h₁ θ' x u)
      (h₂ x)
      (Filter.Eventually.of_forall fun u θ' _ => ((h₀ x u) θ').hasFDerivAt)
  simp_rw [EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb.All_EqWithDensity
    (M := M) h₀ θ x]
  have e := hF.fderiv
  simp_rw [M.policy.integral_eq_one, fderiv_const_apply] at e
  exact e.symm


-- created on 2026-10-20
