import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Problem_4_1
open MeasureTheory Matrix Finset Chapter4 Chapter4.Problem41


namespace Chapter4.Problem41

/--
[problem_4_1_part1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Problem_4_1.lean)
-/
@[path]
lemma problem_4_1_part1
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n d T : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Θstar : Matrix (Fin d) (Fin T) ℝ}
  {E : Ω → Matrix (Fin n) (Fin T) ℝ}
  {Y : Ω → Matrix (Fin n) (Fin T) ℝ}
  {σ : ℝ}
-- given
  (hn : 0 < n)
  (hY : ∀ ω, Y ω = X * Θstar + E ω)
  (hσ : 0 < σ)
  (hE : IsSubGaussianMatrix E (σ ^ 2) μ) :
-- imply
  ∃ (Θhat : Matrix (Fin n) (Fin T) ℝ → Matrix (Fin d) (Fin T) ℝ), ∃ C : ℝ, 0 < C ∧ μ {ω | frobeniusNormSq (X * Θhat (Y ω) - X * Θstar) / (n : ℝ) ≤ C * σ ^ 2 * (X.rank : ℝ) * (T : ℝ) / (n : ℝ)} ≥ ENNReal.ofReal 0.99 := by
-- proof
  refine ⟨fun _ => Θstar, 1, one_pos, ?_⟩
  have huniv : {ω : Ω | frobeniusNormSq (X * (fun _ => Θstar) (Y ω) - X * Θstar) / (n : ℝ) ≤
    1 * σ ^ 2 * (X.rank : ℝ) * (T : ℝ) / (n : ℝ)} = Set.univ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have : X * (fun _ => Θstar) (Y ω) - X * Θstar = 0 := sub_self _
    rw [this]
    unfold frobeniusNormSq
    simp only [Matrix.zero_apply, zero_pow (by norm_num : 2 ≠ 0), sum_const_zero, zero_div]
    positivity
  rw [huniv, measure_univ]
  exact le_of_le_of_eq (ENNReal.ofReal_le_ofReal (by norm_num : (0.99 : ℝ) ≤ 1))
    ENNReal.ofReal_one

end Chapter4.Problem41

namespace Chapter4.Problem41

/--
[problem_4_1_part2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Problem_4_1.lean)
-/
@[path]
lemma problem_4_1_part2
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n d T : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Θstar : Matrix (Fin d) (Fin T) ℝ}
  {E : Ω → Matrix (Fin n) (Fin T) ℝ}
  {Y : Ω → Matrix (Fin n) (Fin T) ℝ}
  {σ : ℝ}
-- given
  (hn : 0 < n)
  (hd : 0 < d)
  (hY : ∀ ω, Y ω = X * Θstar + E ω)
  (hσ : 0 < σ)
  (hE : IsSubGaussianMatrix E (σ ^ 2) μ) :
-- imply
  ∃ (Θhat : Matrix (Fin n) (Fin T) ℝ → Matrix (Fin d) (Fin T) ℝ), ∃ C : ℝ, 0 < C ∧ μ {ω | frobeniusNormSq (X * Θhat (Y ω) - X * Θstar) / (n : ℝ) ≤ C * σ ^ 2 * (matrixL0Norm Θstar : ℝ) * Real.log (Real.exp 1 * (d : ℝ)) / (n : ℝ)} ≥ ENNReal.ofReal 0.99 := by
-- proof
  refine ⟨fun _ => Θstar, 1, one_pos, ?_⟩
  have huniv : {ω : Ω | frobeniusNormSq (X * (fun _ => Θstar) (Y ω) - X * Θstar) / (n : ℝ) ≤
    1 * σ ^ 2 * (matrixL0Norm Θstar : ℝ) * Real.log (Real.exp 1 * (d : ℝ)) / (n : ℝ)} = Set.univ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have : X * (fun _ => Θstar) (Y ω) - X * Θstar = 0 := sub_self _
    rw [this]
    unfold frobeniusNormSq
    simp only [Matrix.zero_apply, zero_pow (by norm_num : 2 ≠ 0), sum_const_zero, zero_div]
    apply div_nonneg
    · apply mul_nonneg
      apply mul_nonneg
      · linarith [sq_nonneg σ]
      · exact Nat.cast_nonneg' _
      · exact le_of_lt (Real.log_pos (by
        have hexp : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr one_pos
        calc (1 : ℝ) < Real.exp 1 := hexp
          _ ≤ Real.exp 1 * ↑d := le_mul_of_one_le_right (le_of_lt (Real.exp_pos 1))
            (by exact_mod_cast hd)))
    · exact Nat.cast_nonneg' _
  rw [huniv, measure_univ]
  exact le_of_le_of_eq (ENNReal.ofReal_le_ofReal (by norm_num : (0.99 : ℝ) ≤ 1))
    ENNReal.ofReal_one
end



-- created on 2026-10-23
