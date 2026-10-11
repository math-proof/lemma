import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch9Entry33Zeta3integral

open Ramanujan.Part1Ch9.Entry33Zeta3integral

/--
[Part1Ch9Entry33Zeta3integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry33Zeta3integral.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry33_zeta3integral_general_eq
-- given
  (n : ℕ) :
-- imply
  IntervalIntegrable (chapter9Entry33WeightedIntegrand n) MeasureTheory.volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (chapter9Entry33Integrand n) MeasureTheory.volume 0 (Real.pi / 2) ∧
    (∫ x in (0 : ℝ)..Real.pi / 2, chapter9Entry33WeightedIntegrand n x) =
      Real.pi / (2 : ℝ) ^ (n + 2) * ((harmonic n : ℚ) : ℝ) ∧
    (∫ x in (0 : ℝ)..Real.pi / 2, chapter9Entry33Integrand n x) =
      1 / (2 : ℝ) ^ (n + 1) * ∑ k ∈ Finset.Icc 1 n, (2 : ℝ) ^ k / (k : ℝ) := by
-- proof
  apply Ramanujan.Part1Ch9.Entry33Zeta3integral.ramanujan_part1_ch9_entry33_zeta3integral_general n

/--
[Part1Ch9Entry33Zeta3integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry33Zeta3integral.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry33_zeta3integral_eq
-- given
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  IntervalIntegrable (chapter9Entry33WeightedIntegrand n) MeasureTheory.volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (chapter9Entry33Integrand n) MeasureTheory.volume 0 (Real.pi / 2) ∧
    (∫ x in (0 : ℝ)..Real.pi / 2, chapter9Entry33WeightedIntegrand n x) =
      Real.pi / (2 : ℝ) ^ (n + 2) * ((harmonic n : ℚ) : ℝ) ∧
    (∫ x in (0 : ℝ)..Real.pi / 2, chapter9Entry33Integrand n x) =
      1 / (2 : ℝ) ^ (n + 1) * ∑ k ∈ Finset.Icc 1 n, (2 : ℝ) ^ k / (k : ℝ) := by
-- proof
  apply Ramanujan.Part1Ch9.Entry33Zeta3integral.ramanujan_part1_ch9_entry33_zeta3integral n hn

-- created on 2026-10-10
