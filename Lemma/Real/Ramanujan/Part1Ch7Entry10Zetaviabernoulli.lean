import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry10Zetaviabernoulli
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry10Zetaviabernoulli


/--
[chapter7Entry10CorollaryLeft_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zetaviabernoulli.lean)
-/
@[path]
private lemma chapter7Entry10CorollaryLeft_one_eq
  {phi : ℂ → ℂ → ℂ}
  {r : ℂ} :
-- imply
  chapter7Entry10CorollaryLeft phi 1 r = 0 := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry10Zetaviabernoulli.chapter7Entry10CorollaryLeft_one phi r

/--
[chapter7Entry10CorollaryRight_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zetaviabernoulli.lean)
-/
@[path]
private lemma chapter7Entry10CorollaryRight_one_eq
  {r : ℂ} :
-- imply
  chapter7Entry10CorollaryRight 1 r = 0 := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry10Zetaviabernoulli.chapter7Entry10CorollaryRight_one r

/--
[chapter7Admissible_neg_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zetaviabernoulli.lean)
-/
@[path]
private lemma chapter7Admissible_neg_div_eq
  {n k : ℕ}
-- given
  (hk : k ∈ Finset.Icc 1 (n - 1)) :
-- imply
  chapter7Admissible (-((k : ℂ) / (n : ℂ))) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry10Zetaviabernoulli.chapter7Admissible_neg_div hk

/--
[chapter7Entry10CorollaryLeft_eq_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zetaviabernoulli.lean)
-/
@[path]
private lemma chapter7Entry10CorollaryLeft_eq_right_eq
  {phi : ℂ → ℂ → ℂ}
  {n : ℕ}
  {r : ℂ}
-- given
  (hphi_series : ∀ r x, r.re < 0 → chapter7Admissible x → HasSum (chapter7PowerDifferenceTerm r x) (phi r x))
  (hr : r.re < -1) :
-- imply
  chapter7Entry10CorollaryLeft phi n r
    = chapter7Entry10CorollaryRight n r := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry10Zetaviabernoulli.chapter7Entry10CorollaryLeft_eq_right phi hphi_series n r hr

/--
[ramanujan_part1_ch7_entry10_zetaviabernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zetaviabernoulli.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry10_zetaviabernoulli_eq
  {phi : ℂ → ℂ → ℂ}
  {n : ℕ}
-- given
  (hphi_entire : ∀ x, chapter7Admissible x → Differentiable ℂ (fun r : ℂ => phi r x))
  (hphi_series : ∀ r x, r.re < 0 → chapter7Admissible x → HasSum (chapter7PowerDifferenceTerm r x) (phi r x))
  (hn : 0 < n) :
-- imply
  MeromorphicOn (chapter7Entry10CorollaryLeft phi n) Set.univ ∧
    MeromorphicOn (chapter7Entry10CorollaryRight n) Set.univ ∧
    chapter7Entry10CorollaryLeft phi n =ᶠ[codiscrete ℂ]
    chapter7Entry10CorollaryRight n := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry10Zetaviabernoulli.ramanujan_part1_ch7_entry10_zetaviabernoulli phi hphi_entire hphi_series n hn

/--
[chapter7Admissible_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zetaviabernoulli.lean)
-/
@[path]
private lemma chapter7Admissible_zero_eq
  :
-- imply
  chapter7Admissible 0 := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7Admissible_zero

/--
[chapter7PowerDifferenceTerm_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zetaviabernoulli.lean)
-/
@[path]
private lemma chapter7PowerDifferenceTerm_zero_left_eq
  {x : ℂ}
  {j : ℕ} :
-- imply
  chapter7PowerDifferenceTerm 0 x j = 0 := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm_zero_left x j

/--
[chapter7PowerDifferenceTerm_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zetaviabernoulli.lean)
-/
@[path]
private lemma chapter7PowerDifferenceTerm_zero_right_eq
  {r : ℂ}
  {j : ℕ} :
-- imply
  chapter7PowerDifferenceTerm r 0 j = 0 := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.chapter7PowerDifferenceTerm_zero_right r j


-- created on 2026-10-20
