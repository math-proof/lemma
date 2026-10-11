import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch9Entry13Bernoulligen

open Ramanujan.Part1Ch9.Entry13Bernoulligen

/--
[Part1Ch9Entry13Bernoulligen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry13Bernoulligen.lean)
-/
@[path]
private lemma chapter9_clausen_term_norm_bound_le
-- given
  (m : ℕ)
  (x : ℝ)
  (k : ℕ) :
-- imply
  ‖chapter9ClausenTerm m x k‖ ≤ 1 / (((k + 1 : ℕ) : ℝ) ^ m) := by
-- proof
  apply Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9ClausenTerm_norm_bound m x k

/--
[Part1Ch9Entry13Bernoulligen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry13Bernoulligen.lean)
-/
@[path]
private lemma chapter9_clausen_term_summable_of_two_le_is
-- given
  (m : ℕ)
  (hm : 2 ≤ m)
  (x : ℝ) :
-- imply
  Summable (chapter9ClausenTerm m x) := by
-- proof
  apply Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9ClausenTerm_summable_of_two_le m x hm

/--
[Part1Ch9Entry13Bernoulligen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry13Bernoulligen.lean)
-/
@[path]
private lemma chapter9_clausen_zero_eq
-- given
  (x : ℝ) :
-- imply
  chapter9Clausen 0 x = 0 := by
-- proof
  apply Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Clausen_zero x

/--
[Part1Ch9Entry13Bernoulligen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry13Bernoulligen.lean)
-/
@[path]
private lemma chapter9_clausen_one_eq
-- given
  (x : ℝ) :
-- imply
  chapter9Clausen 1 x = -Real.log |2 * Real.sin (x / 2)| := by
-- proof
  apply Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Clausen_one x

/--
[Part1Ch9Entry13Bernoulligen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry13Bernoulligen.lean)
-/
@[path]
private lemma chapter9_clausen_of_two_le_eq
-- given
  (m : ℕ)
  (hm : 2 ≤ m)
  (x : ℝ) :
-- imply
  chapter9Clausen m x = ∑' k : ℕ, chapter9ClausenTerm m x k := by
-- proof
  apply Ramanujan.Part1Ch9.Entry13Bernoulligen.chapter9Clausen_of_two_le m x hm

/--
[Part1Ch9Entry13Bernoulligen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry13Bernoulligen.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry13_bernoulli_gen_eq
-- given
  (n : ℕ)
  (x : ℝ)
  (hn : 1 ≤ n)
  (hx0 : x ≠ 0)
  (hx : |x| < 2 * Real.pi) :
-- imply
  IntervalIntegrable (chapter9Entry13Integrand n) MeasureTheory.volume 0 x ∧
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
      Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ))
      Filter.atTop (nhds (chapter9Clausen 1 x)) ∧
    (∀ m : ℕ, 2 ≤ m → m ≤ n + 1 →
      Summable (chapter9ClausenTerm m x)) ∧
    (∫ u in (0 : ℝ)..x, chapter9Entry13Integrand n u) =
      Real.cos (n * Real.pi / 2) * n.factorial * (riemannZeta ((n + 1 : ℕ) : ℂ)).re -
        ∑ j ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ (j * (j + 1) / 2) *
            (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
              x ^ (n - j) * chapter9Clausen (j + 1) x := by
-- proof
  apply Ramanujan.Part1Ch9.Entry13Bernoulligen.ramanujan_part1_ch9_entry13_bernoulligen n x hn hx0 hx

-- created on 2026-10-10
