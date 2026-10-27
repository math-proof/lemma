import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch6Entry6Harmonic

open scoped ContDiff
open Ramanujan.Part1Ch6.Entry6Harmonic

/--
[Part1Ch6Entry6Harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry6Harmonic.lean)
-/
@[path]
private lemma chapter6_partial_sum_zero_eq
-- given
  (f : ℝ → ℝ) :
-- imply
  chapter6PartialSum f 0 = 0 := by
-- proof
  apply Ramanujan.Part1Ch6.Entry6Harmonic.chapter6PartialSum_zero f

/--
[Part1Ch6Entry6Harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry6Harmonic.lean)
-/
@[path]
private lemma chapter6_partial_sum_succ_eq
-- given
  (f : ℝ → ℝ)
  (m : ℕ) :
-- imply
  chapter6PartialSum f (m + 1) = chapter6PartialSum f m + f (m + 1) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry6Harmonic.chapter6PartialSum_succ f m

/--
[Part1Ch6Entry6Harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry6Harmonic.lean)
-/
@[path]
private lemma has_sum_chapter6_derived_series_constant_is
-- given
  (f : ℝ → ℝ)
  (q : ℕ)
  (h : Summable (chapter6ShiftedDerivedSeriesTerm f q 0)) :
-- imply
  HasSum (chapter6ShiftedDerivedSeriesTerm f q 0) (chapter6DerivedSeriesConstant f q) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry6Harmonic.hasSum_chapter6DerivedSeriesConstant f q h

/--
[Part1Ch6Entry6Harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry6Harmonic.lean)
-/
@[path]
private lemma chapter6_convergent_sum_extension_zero_eq
-- given
  (f : ℝ → ℝ) :
-- imply
  chapter6ConvergentSumExtension f 0 = 0 := by
-- proof
  apply Ramanujan.Part1Ch6.Entry6Harmonic.chapter6ConvergentSumExtension_zero f

/--
[Part1Ch6Entry6Harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry6Harmonic.lean)
-/
@[path]
private lemma chapter6_convergent_sum_extension_sub_sub_one_eq
-- given
  (f : ℝ → ℝ)
  (x : ℝ)
  (h : Summable (chapter6ShiftedDerivedSeriesTerm f 0 (x - 1))) :
-- imply
  chapter6ConvergentSumExtension f x - chapter6ConvergentSumExtension f (x - 1) = f x := by
-- proof
  apply Ramanujan.Part1Ch6.Entry6Harmonic.chapter6ConvergentSumExtension_sub_sub_one f x h

/--
[Part1Ch6Entry6Harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry6Harmonic.lean)
-/
@[path]
private lemma summable_chapter6_shifted_derived_series_term_nat_cast_is
-- given
  (f : ℝ → ℝ)
  (q : ℕ)
  (h : Summable (chapter6ShiftedDerivedSeriesTerm f q 0))
  (m : ℕ) :
-- imply
  Summable (chapter6ShiftedDerivedSeriesTerm f q m) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry6Harmonic.summable_chapter6ShiftedDerivedSeriesTerm_natCast f q h m

/--
[Part1Ch6Entry6Harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry6Harmonic.lean)
-/
@[path]
private lemma chapter6_convergent_sum_extension_nat_cast_eq
-- given
  (f : ℝ → ℝ)
  (h : Summable (chapter6ShiftedDerivedSeriesTerm f 0 0))
  (m : ℕ) :
-- imply
  chapter6ConvergentSumExtension f m = chapter6PartialSum f m := by
-- proof
  apply Ramanujan.Part1Ch6.Entry6Harmonic.chapter6ConvergentSumExtension_natCast f h m

/--
[Part1Ch6Entry6Harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry6Harmonic.lean)
-/
@[path]
private lemma iterated_deriv_chapter6_convergent_sum_extension_apply_zero_eq
-- given
  (f : ℝ → ℝ)
  (rho : ℝ)
  (n : ℕ)
  (hrho : 0 < rho)
  (hsmooth : ContDiff ℝ ∞ f)
  (hsummable : ∀ q : ℕ, Summable (chapter6ShiftedDerivedSeriesTerm f q 0))
  (hdominated : ∀ q : ℕ, 0 < q →
    ∃ bound : ℕ → ℝ,
      Summable bound ∧ ∀ x ∈ Set.Icc (-rho) rho, ∀ k : ℕ,
        |chapter6ShiftedDerivedSeriesTerm f q x k| ≤ bound k)
  (hn : 0 < n) :
-- imply
  iteratedDeriv n (chapter6ConvergentSumExtension f) 0 =
    -chapter6DerivedSeriesConstant f n := by
-- proof
  apply Ramanujan.Part1Ch6.Entry6Harmonic.iteratedDeriv_chapter6ConvergentSumExtension_apply_zero f rho hrho hsmooth hsummable hdominated n hn

/--
[Part1Ch6Entry6Harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry6Harmonic.lean)
-/
@[path]
private lemma exists_has_sum_chapter6_entry6_term_eq
-- given
  (f : ℝ → ℝ)
  (rho : ℝ)
  (hrho : 0 < rho)
  (hsmooth : ContDiff ℝ ∞ f)
  (hsummable : ∀ q : ℕ, Summable (chapter6ShiftedDerivedSeriesTerm f q 0))
  (hdominated : ∀ q : ℕ, 0 < q →
    ∃ bound : ℕ → ℝ,
      Summable bound ∧ ∀ x ∈ Set.Icc (-rho) rho, ∀ k : ℕ,
        |chapter6ShiftedDerivedSeriesTerm f q x k| ≤ bound k)
  (hanalytic : AnalyticAt ℝ (chapter6ConvergentSumExtension f) 0) :
-- imply
  ∃ r : ℝ, 0 < r ∧ r ≤ rho ∧
    ∀ x : ℝ, |x| < r →
      HasSum (chapter6Entry6Term f x) (chapter6ConvergentSumExtension f x) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry6Harmonic.exists_hasSum_chapter6Entry6Term f rho hrho hsmooth hsummable hdominated hanalytic

/--
[Part1Ch6Entry6Harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry6Harmonic.lean)
-/
@[path]
private lemma ramanujan_part1_ch6_entry6_harmonic_eq
-- given
  (f : ℝ → ℝ)
  (rho : ℝ)
  (hrho : 0 < rho)
  (hsmooth : ContDiff ℝ ∞ f)
  (hsummable : ∀ q : ℕ, ∀ x : ℝ,
    Summable (chapter6ShiftedDerivedSeriesTerm f q x))
  (hdominated : ∀ q : ℕ,
    ∃ bound : ℕ → ℝ,
      Summable bound ∧ ∀ x ∈ Set.Icc (-rho) rho, ∀ k : ℕ,
        |chapter6ShiftedDerivedSeriesTerm f q x k| ≤ bound k)
  (hanalytic : AnalyticAt ℝ (chapter6ConvergentSumExtension f) 0) :
-- imply
  (∀ n : ℕ, HasSum (chapter6ShiftedDerivedSeriesTerm f n 0) (chapter6DerivedSeriesConstant f n)) ∧
    chapter6ConvergentSumExtension f 0 = 0 ∧
    (∀ x : ℝ, chapter6ConvergentSumExtension f x - chapter6ConvergentSumExtension f (x - 1) = f x) ∧
    (∀ m : ℕ, chapter6ConvergentSumExtension f m = chapter6PartialSum f m) ∧
    (∀ n : ℕ, 0 < n →
      iteratedDeriv n (chapter6ConvergentSumExtension f) 0 = -chapter6DerivedSeriesConstant f n) ∧
    ∃ r : ℝ, 0 < r ∧ r ≤ rho ∧
      ∀ x : ℝ, |x| < r →
        HasSum (chapter6Entry6Term f x) (chapter6ConvergentSumExtension f x) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry6Harmonic.ramanujan_part1_ch6_entry6_harmonic f rho hrho hsmooth hsummable hdominated hanalytic

-- created on 2026-10-10
