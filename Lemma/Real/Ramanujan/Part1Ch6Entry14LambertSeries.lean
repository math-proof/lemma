import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch6Entry14LambertSeries
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open Entry10Centralbinomialfull
open Entry10Centralbinomialexpansion


/--
[summable_chapter6Entry14MinusTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry14LambertSeries.lean)
-/
@[path]
private lemma summable_chapter6Entry14MinusTerm_eq
  {x : ℝ}
-- given
  (hx : 0 < x) :
-- imply
  Summable (chapter6Entry14MinusTerm x) := by
-- proof
  apply Entry10Centralbinomialfull.summable_chapter6Entry14MinusTerm x hx

/--
[chapter6Entry14MinusSum_error_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry14LambertSeries.lean)
-/
@[path]
private lemma chapter6Entry14MinusSum_error_le_eq
  {x : ℝ}
  {n : ℕ}
-- given
  (hx : 0 < x)
  (hn : 1 ≤ n) :
-- imply
  |chapter6Entry14MinusSum x -
    (Real.eulerMascheroniConstant / x - Real.log x / x + 1 / 4 -
    chapter6Entry14MinusCorrection n x)| ≤
    |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
    x ^ (2 * n) / ((2 * n).factorial : ℝ) *
    (x ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6) := by
-- proof
  apply Entry10Centralbinomialfull.chapter6Entry14MinusSum_error_le x n hx hn

/--
[ramanujan_part1_ch6_entry10_centralbinomialfull](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry14LambertSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch6_entry10_centralbinomialfull_eq
  {x : ℝ}
  {n : ℕ}
-- given
  (hx : 0 < x)
  (hn : 1 ≤ n) :
-- imply
  Summable (chapter6Entry14MinusTerm x) ∧
    |chapter6Entry14MinusSum x -
    (Real.eulerMascheroniConstant / x - Real.log x / x + 1 / 4 -
    chapter6Entry14MinusCorrection n x)| ≤
    |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
    x ^ (2 * n) / ((2 * n).factorial : ℝ) *
    (x ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6) := by
-- proof
  apply Entry10Centralbinomialfull.ramanujan_part1_ch6_entry10_centralbinomialfull x n hx hn

/--
[summable_chapter6Entry14PlusTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry14LambertSeries.lean)
-/
@[path]
private lemma summable_chapter6Entry14PlusTerm_eq
  {x : ℝ}
-- given
  (hx : 0 < x) :
-- imply
  Summable (chapter6Entry14PlusTerm x) := by
-- proof
  apply Entry10Centralbinomialexpansion.summable_chapter6Entry14PlusTerm x hx

/--
[ramanujan_part1_ch6_entry10_centralbinomialexpansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry14LambertSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch6_entry10_centralbinomialexpansion_eq
  {x : ℝ}
  {n : ℕ}
-- given
  (hx : 0 < x)
  (hn : 1 ≤ n) :
-- imply
  Summable (chapter6Entry14PlusTerm x) ∧
    |chapter6Entry14PlusSum x -
    (Real.log 2 / x - 1 / 4 + chapter6Entry14PlusCorrection n x)| ≤
    |(bernoulli (2 * n) : ℝ) * (bernoulli (2 * n + 2) : ℝ)| *
    x ^ (2 * n) / ((2 * n).factorial : ℝ) *
    (x ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6 +
    (2 : ℝ) ^ (2 * n + 1) *
    (x ^ 2 / Real.pi ^ 2 + Real.pi ^ 2 / 6)) := by
-- proof
  apply Entry10Centralbinomialexpansion.ramanujan_part1_ch6_entry10_centralbinomialexpansion x n hx hn


-- created on 2026-10-20
