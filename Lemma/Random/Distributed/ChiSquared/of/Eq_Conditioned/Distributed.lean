import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
Independent standard normals have `∑ x i²` of expectation equal to the degrees of freedom.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ι → Ω → ℝ} [Fintype ι]
-- given
  (_ : Pairwise fun i j => x i ⟂ᵢ[π] x j)
  (h₀ : ∀ i, HasLaw (x i) (gaussianReal 0 1) π) :
-- imply
  ∫ ω, ∑ i, (x i ω) ^ 2 ∂π = Fintype.card ι := by
-- proof
  have h₁ : ∀ i, ∫ ω, (x i ω) ^ 2 ∂π = 1 := by
    intro i
    have hvar : variance (x i) π = 1 := by
      rw [← variance_id_map (h₀ i).aemeasurable, (h₀ i).map_eq, variance_id_gaussianReal]
      simp
    have hmean : ∫ ω, x i ω ∂π = 0 := by
      simpa [integral_id_gaussianReal, Function.comp_def] using
        (h₀ i).integral_comp (f := id) (by fun_prop)
    have hmem : MemLp (x i) 2 π := by
      simpa [Function.comp_def] using (h₀ i).memLp_comp (memLp_id_gaussianReal 2)
    rw [← hvar, variance_eq_sub hmem, hmean]
    simp
  have hint : ∀ i, Integrable (fun ω => (x i ω) ^ 2) π := by
    intro i
    simpa [Function.comp_def] using ((h₀ i).memLp_comp (memLp_id_gaussianReal 2)).integrable_sq
  rw [integral_finsetSum Finset.univ fun i _ => hint i]
  simp [h₁, Finset.sum_const, Finset.card_univ]


-- created on 2026-10-11
-- updated on 2026-10-17
