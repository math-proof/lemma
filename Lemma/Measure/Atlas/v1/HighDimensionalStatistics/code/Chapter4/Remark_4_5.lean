import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Remark_4_5
open Chapter4
open Matrix Finset


namespace Chapter4

/--
[frobeniusNormSq_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Remark_4_5.lean)
-/
@[path]
lemma frobeniusNormSq_nonneg
  {m p : ℕ}
  {A : Matrix (Fin m) (Fin p) ℝ} :
-- imply
  0 ≤ frobeniusNormSq A := by
-- proof
  unfold frobeniusNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

end Chapter4

namespace Chapter4

/--
[frobeniusNormSq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Remark_4_5.lean)
-/
@[path]
lemma frobeniusNormSq_zero
  {m p : ℕ} :
-- imply
  frobeniusNormSq (0 : Matrix (Fin m) (Fin p) ℝ) = 0 := by
-- proof
  unfold frobeniusNormSq
  simp [Matrix.zero_apply, sq]

end Chapter4

namespace Chapter4

/--
[rectOpNorm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Remark_4_5.lean)
-/
@[path]
lemma rectOpNorm_zero
  {m p : ℕ} :
-- imply
  rectOpNorm (0 : Matrix (Fin m) (Fin p) ℝ) = 0 := by
-- proof
  simp [rectOpNorm, map_zero]

end Chapter4

namespace Chapter4

/--
[nuclearNorm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Remark_4_5.lean)
-/
@[path]
lemma nuclearNorm_nonneg
  {d T : ℕ}
  {Θ : Matrix (Fin d) (Fin T) ℝ} :
-- imply
  0 ≤ nuclearNorm Θ := by
-- proof
  unfold nuclearNorm
  by_cases h : BddAbove { t : ℝ | ∃ B : Matrix (Fin d) (Fin T) ℝ, rectOpNorm B ≤ 1 ∧
    t = ∑ i, ∑ j, B i j * Θ i j }
  · apply le_csSup_of_le h
    · show ∃ B : Matrix (Fin d) (Fin T) ℝ, rectOpNorm B ≤ 1 ∧
      (0 : ℝ) = ∑ i, ∑ j, B i j * Θ i j
      exact ⟨0, by rw [rectOpNorm_zero]; exact zero_le_one, by simp⟩
    · exact le_refl 0
  · simp [csSup_of_not_bddAbove h, Real.sSup_empty]

end Chapter4


-- created on 2026-10-23
