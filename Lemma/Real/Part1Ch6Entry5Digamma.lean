import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch6Entry5Digamma

open Ramanujan.Part1Ch6.Entry5Digamma

/--
[Part1Ch6Entry5Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry5Digamma.lean)
-/
@[path]
private lemma summable_chapter6_section13_example_c_term_eq
-- given
  (x : ℝ)
  (hx : 0 < x) :
-- imply
  Summable (chapter6Section13ExampleCTerm x) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry5Digamma.summable_chapter6Section13ExampleCTerm x hx

/--
[Part1Ch6Entry5Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry5Digamma.lean)
-/
@[path]
private lemma chapter6_section13_example_c_term_zero_eq
-- given
  (x : ℝ) :
-- imply
  chapter6Section13ExampleCTerm x 0 = 1 / (x + 1) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry5Digamma.chapter6Section13ExampleCTerm_zero x

/--
[Part1Ch6Entry5Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry5Digamma.lean)
-/
@[path]
private lemma chapter6_section13_example_c_term_succ_eq
-- given
  (x : ℝ)
  (j : ℕ) :
-- imply
  chapter6Section13ExampleCTerm x (j + 1) =
    (-1 / (x + 1)) * chapter6Section13ExampleCTerm (x + 1) j := by
-- proof
  apply Ramanujan.Part1Ch6.Entry5Digamma.chapter6Section13ExampleCTerm_succ x j

/--
[Part1Ch6Entry5Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry5Digamma.lean)
-/
@[path]
private lemma chapter6_section13_example_c_sum_eq_eq
-- given
  (x : ℝ)
  (hx : 0 < x) :
-- imply
  chapter6Section13ExampleCSum x =
    1 / (x + 1) - chapter6Section13ExampleCSum (x + 1) / (x + 1) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry5Digamma.chapter6Section13ExampleCSum_eq x hx

/--
[Part1Ch6Entry5Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry5Digamma.lean)
-/
@[path]
private lemma is_big_o_chapter6_section13_example_c_sum_sub_sum_bell_eq
-- given
  (N : ℕ) :
-- imply
  Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ => chapter6Section13ExampleCSum x -
      ∑ j ∈ Finset.range N, (-1 : ℝ) ^ j * ((j + 1).bell : ℝ) / x ^ (j + 1))
    (fun x : ℝ => 1 / x ^ (N + 1)) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry5Digamma.isBigO_chapter6Section13ExampleCSum_sub_sum_bell N

/--
[Part1Ch6Entry5Digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry5Digamma.lean)
-/
@[path]
private lemma ramanujan_part1_ch6_entry5_digamma_eq :
-- imply
  (∀ᶠ x : ℝ in Filter.atTop,
      0 < x ∧ Summable (chapter6Section13ExampleCTerm x)) ∧
    ∀ N : ℕ,
      Asymptotics.IsBigO Filter.atTop
        (fun x : ℝ => chapter6Section13ExampleCSum x -
          ∑ j ∈ Finset.range N, (-1 : ℝ) ^ j * ((j + 1).bell : ℝ) / x ^ (j + 1))
        (fun x : ℝ => 1 / x ^ (N + 1)) := by
-- proof
  apply Ramanujan.Part1Ch6.Entry5Digamma.ramanujan_part1_ch6_entry5_digamma

-- created on 2026-10-10
