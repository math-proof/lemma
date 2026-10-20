import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry1SeriesTransformation
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry1SeriesTransformation


/--
[ramanujan_part1_ch3_entry1_series_transformation_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1SeriesTransformation.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry1_series_transformation_general_eq
  {R₁ : ℝ}
  {f : ℂ → ℂ}
  {Q : ℕ → ℂ}
-- given
  (hR₁ : 1 < R₁)
  (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R₁))
  (hSumm : Summable (fun p : ℕ × ℕ => Q p.1 * iteratedDeriv (p.1 + p.2) f (0 : ℂ) / ((Nat.factorial p.2 : ℂ)))) :
-- imply
  ∃ v : ℂ,
    HasSum (fun n : ℕ => (∑ j ∈ Finset.range (n + 1), Q j / ((Nat.factorial (n - j) : ℂ))) *
    iteratedDeriv n f (0 : ℂ)) v ∧
    HasSum (fun n : ℕ => Q n * iteratedDeriv n f (1 : ℂ)) v := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation.ramanujan_part1_ch3_entry1_series_transformation_general R₁ hR₁ f hf Q hSumm

/--
[ramanujan_part1_ch3_entry1_series_transformation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1SeriesTransformation.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry1_series_transformation_eq
  {R₁ : ℝ}
  {f : ℂ → ℂ}
  {Q : ℕ → ℂ}
-- given
  (hR₁ : 1 < R₁)
  (hf : AnalyticOn ℂ f (Metric.ball (0 : ℂ) R₁))
  (hQ : ∃ R₂ : ℝ, 0 < R₂ ∧ ∀ z : ℂ, ‖z‖ < R₂ → Summable (fun n : ℕ => Q n * z ^ n))
  (hSumm : Summable (fun p : ℕ × ℕ => Q p.1 * iteratedDeriv (p.1 + p.2) f (0 : ℂ) / ((Nat.factorial p.2 : ℂ)))) :
-- imply
  ∃ v : ℂ,
    HasSum (fun n : ℕ => (∑ j ∈ Finset.range (n + 1), Q j / ((Nat.factorial (n - j) : ℂ))) *
    iteratedDeriv n f (0 : ℂ)) v ∧
    HasSum (fun n : ℕ => Q n * iteratedDeriv n f (1 : ℂ)) v := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry1SeriesTransformation.ramanujan_part1_ch3_entry1_series_transformation R₁ hR₁ f hf Q hQ hSumm


-- created on 2026-10-20
