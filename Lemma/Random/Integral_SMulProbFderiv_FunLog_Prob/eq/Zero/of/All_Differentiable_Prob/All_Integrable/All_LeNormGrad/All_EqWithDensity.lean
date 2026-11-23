import Def.Analysis.Calculus.Gradient.Operators
import Mathlib.Analysis.Calculus.ParametricIntegral
import Lemma.Random.EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb.All_EqWithDensity
import Lemma.Real.StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
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
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [MeasurableSpace 𝒮] [μ : ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy]
-- given
  (h₀ : ∀ sₜ aₜ, Differentiable ℝ (fun θ => M.π θ sₜ aₜ))
  (h₁ : ∀ sₜ, Integrable (fun aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖)) μ.measure)
  (hBdd : ∀ sₜ aₜ, BddAbove (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖))
  (θ : Θ)
  (sₜ : 𝒮) :
-- imply
  ∫ u, M.π θ sₜ u • fderiv ℝ (fun θ' => Real.log (M.π θ' sₜ u)) θ
    ∂μ.measure = 0 := by
-- proof
  let g : 𝒮 → 𝒜 → ℝ :=
    fun sₜ aₜ => sSup (Set.range fun θ => ‖∇[θ] M.π θ sₜ aₜ‖)
  have hBound : ∀ θ sₜ aₜ, ‖fderiv ℝ (fun θ => M.π θ sₜ aₜ) θ‖ ≤ g sₜ aₜ := by
    intro θ sₜ aₜ
    have : ‖∇[θ] M.π θ sₜ aₜ‖ ≤ g sₜ aₜ := by
      refine le_csSup ?_ ⟨θ, rfl⟩
      exact hBdd sₜ aₜ
    simpa [gradient, LinearIsometryEquiv.norm_map] using this
  have hSf : StronglyMeasurable (fun u => fderiv ℝ (fun θ => M.π θ sₜ u) θ) :=
    StronglyMeasurable_Fderiv.of.All_DifferentiableAt.All_Measurable
      (fun θ' => (hStoch.measurable_π θ').comp measurable_prodMk_left)
      (fun u => (h₀ sₜ u) θ)
  have h1 : ∫ aₜ, M.π θ sₜ aₜ ∂ReferenceMeasure.measure = 1 :=
    hStoch.integral_eq_one θ sₜ
  have hIπ : Integrable (M.π θ sₜ) ReferenceMeasure.measure :=
    Integrable.of_integral_ne_zero (by rw [h1]; exact one_ne_zero)
  have hF : HasFDerivAt (fun θ' => ∫ u, M.π θ' sₜ u ∂ReferenceMeasure.measure)
      (∫ u, fderiv ℝ (fun θ' => M.π θ' sₜ u) θ ∂ReferenceMeasure.measure) θ :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun θ' u => M.π θ' sₜ u)
      (F' := fun θ' u => fderiv ℝ (fun θ'' => M.π θ'' sₜ u) θ')
      (s := Set.univ) (bound := g sₜ) Filter.univ_mem
      (Filter.Eventually.of_forall fun θ' =>
        ((hStoch.measurable_π θ').comp measurable_prodMk_left).aestronglyMeasurable)
      hIπ
      hSf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u θ' _ => hBound θ' sₜ u)
      (h₁ sₜ)
      (Filter.Eventually.of_forall fun u θ' _ => ((h₀ sₜ u) θ').hasFDerivAt)
  simp_rw [EqSMulProb_FderivLog_Prob_Fderiv_FunProb.of.All_All_Differentiable_FunPolProb.All_EqWithDensity
    (M := M) h₀ θ sₜ]
  have e := hF.fderiv
  have hint : (fun θ' => ∫ u, M.π θ' sₜ u ∂ReferenceMeasure.measure) =
      fun _ => (1 : ℝ) := funext fun θ' => hStoch.integral_eq_one θ' sₜ
  rw [hint, fderiv_const_apply] at e
  exact e.symm


-- created on 2026-10-20
-- updated on 2026-11-17