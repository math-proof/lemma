/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch9Entry14Xoversin.lean -/


import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry14Xoversin
import Lemma.Real.Ramanujan.Part1Ch9Entry14Xoversin

namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch9Entry14Xoversin

open scoped Interval
open Filter Finset MeasureTheory Topology
open MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen
open MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry14Xoversin

example (m : ℕ) (x : ℝ) (k : ℕ) :
    ‖chapter9OddClausenTerm m x k‖ ≤ 1 / (((2 * k + 1 : ℕ) : ℝ) ^ m) :=
  chapter9OddClausenTerm_norm_bound m x k

example (x : ℝ) : Summable (chapter9OddClausenTerm 2 x) :=
  chapter9OddClausenTerm_summable_of_two_le 2 x le_rfl

example (x : ℝ) : chapter9OddClausen 0 x = 0 := chapter9OddClausen_zero x

example (x : ℝ) :
    chapter9OddClausen 1 x = -(1 / 2 : ℝ) * Real.log |Real.tan (x / 2)| :=
  chapter9OddClausen_one x

example (m : ℕ) (x : ℝ) (hm : 2 ≤ m) :
    chapter9OddClausen m x = ∑' k : ℕ, chapter9OddClausenTerm m x k :=
  chapter9OddClausen_of_two_le m x hm

example (m : ℕ) (x : ℝ) (hm : 2 ≤ m) :
    chapter9OddClausen m x = chapter9Clausen m x -
      (1 / (2 : ℝ) ^ m) * chapter9Clausen m (2 * x) :=
  chapter9OddClausen_eq_clausen_sub_of_two_le m x hm

example (x : ℝ) (hx0 : x ≠ 0) (hx : |x| < Real.pi) :
    chapter9OddClausen 1 x = chapter9Clausen 1 x -
      (1 / (2 : ℝ) ^ (1 : ℕ)) * chapter9Clausen 1 (2 * x) :=
  chapter9OddClausen_eq_clausen_sub 1 x le_rfl hx0 hx

example (m : ℕ) (hm : 2 ≤ m) :
    chapter9ChiAtOne m =
      (1 - 1 / (2 : ℝ) ^ m) * (riemannZeta (m : ℂ)).re :=
  chapter9ChiAtOne_eq_zeta m hm

-- Entry 14 supplies interval integrability at `n = 1`.
example (x : ℝ) (hx0 : x ≠ 0) (hx : |x| < Real.pi) :
    IntervalIntegrable (chapter9Entry14Integrand 1) volume 0 x :=
  (ramanujan_part1_ch9_entry14_xoversin 1 x (by norm_num) hx0 hx).1

-- Entry 14 identifies the odd harmonic cosine limit at `n = 1`.
example (x : ℝ) (hx0 : x ≠ 0) (hx : |x| < Real.pi) :
    Tendsto
      (fun N : ℕ => ∑ k ∈ range N,
        Real.cos (((2 * k + 1 : ℕ) : ℝ) * x) / ((2 * k + 1 : ℕ) : ℝ))
      atTop (𝓝 (chapter9OddClausen 1 x)) :=
  (ramanujan_part1_ch9_entry14_xoversin 1 x (by norm_num) hx0 hx).2.2.1

end MathlibExtTest.Analysis.Ramanujan.Part1Ch9Entry14Xoversin
