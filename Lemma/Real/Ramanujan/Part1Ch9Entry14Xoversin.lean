import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry14Xoversin
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen
open MathlibExt.Analysis.Ramanujan.Part1Ch9
open Entry14Xoversin


/--
[chapter9OddClausenTerm_norm_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry14Xoversin.lean)
-/
@[path]
private lemma chapter9OddClausenTerm_norm_bound_eq
  {m : ℕ}
  {x : ℝ}
  {k : ℕ} :
-- imply
  ‖chapter9OddClausenTerm m x k‖ ≤ 1 / (((2 * k + 1 : ℕ) : ℝ) ^ m) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry14Xoversin.chapter9OddClausenTerm_norm_bound m x k

/--
[chapter9OddClausenTerm_summable_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry14Xoversin.lean)
-/
@[path]
private lemma chapter9OddClausenTerm_summable_of_two_le_eq
  {m : ℕ}
  {x : ℝ}
-- given
  (hm : 2 ≤ m) :
-- imply
  Summable (chapter9OddClausenTerm m x) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry14Xoversin.chapter9OddClausenTerm_summable_of_two_le m x hm

/--
[chapter9OddClausen_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry14Xoversin.lean)
-/
@[path]
private lemma chapter9OddClausen_zero_eq
  {x : ℝ} :
-- imply
  chapter9OddClausen 0 x = 0 := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry14Xoversin.chapter9OddClausen_zero x

/--
[chapter9OddClausen_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry14Xoversin.lean)
-/
@[path]
private lemma chapter9OddClausen_one_eq
  {x : ℝ} :
-- imply
  chapter9OddClausen 1 x = -(1 / 2 : ℝ) * Real.log |Real.tan (x / 2)| := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry14Xoversin.chapter9OddClausen_one x

/--
[chapter9OddClausen_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry14Xoversin.lean)
-/
@[path]
private lemma chapter9OddClausen_of_two_le_eq
  {m : ℕ}
  {x : ℝ}
-- given
  (hm : 2 ≤ m) :
-- imply
  chapter9OddClausen m x = ∑' k : ℕ, chapter9OddClausenTerm m x k := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry14Xoversin.chapter9OddClausen_of_two_le m x hm

/--
[chapter9OddClausen_eq_clausen_sub_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry14Xoversin.lean)
-/
@[path]
private lemma chapter9OddClausen_eq_clausen_sub_of_two_le_eq
  {m : ℕ}
  {x : ℝ}
-- given
  (hm : 2 ≤ m) :
-- imply
  chapter9OddClausen m x = chapter9Clausen m x -
    (1 / (2 : ℝ) ^ m) * chapter9Clausen m (2 * x) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry14Xoversin.chapter9OddClausen_eq_clausen_sub_of_two_le m x hm

/--
[chapter9OddClausen_eq_clausen_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry14Xoversin.lean)
-/
@[path]
private lemma chapter9OddClausen_eq_clausen_sub_eq
  {m : ℕ}
  {x : ℝ}
-- given
  (hm : 1 ≤ m)
  (hx0 : x ≠ 0)
  (hx : |x| < Real.pi) :
-- imply
  chapter9OddClausen m x = chapter9Clausen m x -
    (1 / (2 : ℝ) ^ m) * chapter9Clausen m (2 * x) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry14Xoversin.chapter9OddClausen_eq_clausen_sub m x hm hx0 hx

/--
[chapter9ChiAtOne_eq_zeta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry14Xoversin.lean)
-/
@[path]
private lemma chapter9ChiAtOne_eq_zeta_eq
  {m : ℕ}
-- given
  (hm : 2 ≤ m) :
-- imply
  chapter9ChiAtOne m =
    (1 - 1 / (2 : ℝ) ^ m) * (riemannZeta (m : ℂ)).re := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry14Xoversin.chapter9ChiAtOne_eq_zeta m hm

/--
[ramanujan_part1_ch9_entry14_xoversin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry14Xoversin.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry14_xoversin_eq
  {n : ℕ}
  {x : ℝ}
-- given
  (hn : 1 ≤ n)
  (hx0 : x ≠ 0)
  (hx : |x| < Real.pi) :
-- imply
  IntervalIntegrable (chapter9Entry14Integrand n) volume 0 x ∧
    Summable (fun k : ℕ =>
    1 / (((2 * k + 1 : ℕ) : ℝ) ^ (n + 1))) ∧
    Tendsto
    (fun N : ℕ => ∑ k ∈ range N,
    Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) /
    ((2 * k + 1 : ℕ) : ℝ))
    atTop (𝓝 (chapter9OddClausen 1 x)) ∧
    (∀ m : ℕ, 2 ≤ m → m ≤ n + 1 →
    Summable (chapter9OddClausenTerm m x)) ∧
    (∫ u in (0 : ℝ)..x, chapter9Entry14Integrand n u) =
    Real.cos (n * Real.pi / 2) * n.factorial *
    chapter9ChiAtOne (n + 1) -
    ∑ j ∈ range (n + 1),
    (-1 : ℝ) ^ (j * (j + 1) / 2) *
    (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
    x ^ (n - j) * chapter9OddClausen (j + 1) x := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry14Xoversin.ramanujan_part1_ch9_entry14_xoversin n x hn hx0 hx


-- created on 2026-10-20
