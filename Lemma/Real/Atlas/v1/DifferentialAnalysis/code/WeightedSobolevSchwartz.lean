import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.WeightedSobolevSchwartz
open SobolevEmbedding
open scoped ZeroAtInfty SchwartzMap


namespace SobolevEmbedding

/--
[schwartz_iteratedFDeriv_memLp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeightedSobolevSchwartz.lean)
-/
@[path]
lemma schwartz_iteratedFDeriv_memLp
  {n : ℕ}
  {g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)}
  {j : ℕ} :
-- imply
  MemLp (fun x => iteratedFDeriv ℝ j (⇑g) x) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
-- proof
  set_option synthInstance.maxHeartbeats 80000 in
  rw [memLp_two_iff_integrable_sq_norm
    ((g.smooth (j : ℕ∞)).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable]
  obtain ⟨C, hCpos, hC⟩ := g.decay 0 j
  simp only [pow_zero, one_mul] at hC
  have hint := g.integrable_pow_mul_iteratedFDeriv volume 0 j
  simp only [pow_zero, one_mul] at hint
  apply Integrable.mono (hint.const_mul C)
  · set_option synthInstance.maxHeartbeats 80000 in
    exact (((g.smooth (j : ℕ∞)).continuous_iteratedFDeriv le_rfl).norm.pow 2).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [norm_mul, Real.norm_of_nonneg hCpos.le, Real.norm_of_nonneg (norm_nonneg _)]
    calc ‖iteratedFDeriv ℝ j (⇑g) x‖ ^ 2
      = ‖iteratedFDeriv ℝ j (⇑g) x‖ * ‖iteratedFDeriv ℝ j (⇑g) x‖ := sq _
      _ ≤ C * ‖iteratedFDeriv ℝ j (⇑g) x‖ := by gcongr; exact hC x
end SobolevEmbedding


/--
[japaneseBracket_pow_ne_zero_complex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WeightedSobolevSchwartz.lean)
-/
@[path]
private lemma japaneseBracket_pow_ne_zero_complex_eq
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin n)}
  {k : ℕ} :
-- imply
  (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) ≠ 0 := by
-- proof
  apply SobolevEmbedding.japaneseBracket_pow_ne_zero_complex x k


-- created on 2026-10-23
