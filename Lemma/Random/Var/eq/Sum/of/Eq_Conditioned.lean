import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import sympy.Basic
open MeasureTheory ProbabilityTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : ι → Ω → ℝ} [Fintype ι]
-- given
  (h₀ : Pairwise fun i j => x i ⟂ᵢ[π] x j)
  (h₁ : ∀ i, MemLp (x i) 2 π) :
-- imply
  variance (fun ω => ∑ i, x i ω) π = ∑ i, variance (x i) π := by
-- proof
  have hfun : (∑ i, x i) = fun ω => ∑ i, x i ω := by
    funext ω
    simp [Finset.sum_apply]
  simpa [hfun] using
    IndepFun.variance_sum (μ := π) (s := Finset.univ) (fun i _ => h₁ i)
      (fun i _ j _ hij => h₀ hij)


-- created on 2023-04-23
-- updated on 2026-10-17
