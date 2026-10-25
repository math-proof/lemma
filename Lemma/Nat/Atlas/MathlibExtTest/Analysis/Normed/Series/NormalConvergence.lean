import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Analysis.Normed.Series.NormalConvergence.Part2
open Topology
open scoped ENNReal


/--
[supNormOn_oneTermSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma supNormOn_oneTermSeries
  {n : ℕ} :
-- imply
  supNormOn (oneTermSeries n) ({0} : Set ℝ) = if n = 0 then (1 : ℝ≥0∞) else 0 := by
-- proof
  have : Nonempty ↥(({0} : Set ℝ)) := ⟨⟨0, rfl⟩⟩
  unfold supNormOn
  by_cases hn : n = 0
  · subst hn
    rw [ite_eq_left rfl]
    have hbody : ∀ x : ↥(({0} : Set ℝ)),
      ENNReal.ofReal ‖oneTermSeries 0 ↑x‖ = 1 := by
      intro x
      change ENNReal.ofReal ‖(if (0 : ℕ) = 0 then (1 : ℝ) else 0)‖ = 1
      rw [ite_eq_left rfl, norm_one, ENNReal.ofReal_one]
    simp only [hbody]
    exact iSup_const
  · rw [ite_eq_right hn]
    have hbody : ∀ x : ↥(({0} : Set ℝ)),
      ENNReal.ofReal ‖oneTermSeries n ↑x‖ = 0 := by
      intro x
      change ENNReal.ofReal ‖(if n = 0 then (1 : ℝ) else 0)‖ = 0
      rw [ite_eq_right hn, norm_zero, ENNReal.ofReal_zero]
    simp only [hbody]
    exact iSup_const

/--
[oneTermSeries_normal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Normed/Series/NormalConvergence.lean)
-/
@[path]
lemma oneTermSeries_normal
-- imply
  ConvergesNormallyOn oneTermSeries ({0} : Set ℝ) := by
-- proof
  unfold ConvergesNormallyOn
  rw [tsum_congr supNormOn_oneTermSeries,
    tsum_eq_single 0 (fun b hb => ite_eq_right hb), ite_eq_left rfl]
  exact ENNReal.one_ne_top


-- created on 2026-10-23
