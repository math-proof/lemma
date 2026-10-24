/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch9Entry13Bernoulligen.lean -/


import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry13Bernoulligen
import Lemma.Real.Part1Ch9Entry13Bernoulligen

/-!
# Ramanujan's Notebooks, Part I, Chapter 9, Entry 13 API checks

Branch equations for `chapter9Clausen`, the Clausen summability and norm bound,
and the Entry 13 integrand equation.
-/

namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch9Entry13Bernoulligen

open MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen

example (x : ℝ) : chapter9Clausen 0 x = 0 := chapter9Clausen_zero x

example (x : ℝ) : chapter9Clausen 1 x = -Real.log |2 * Real.sin (x / 2)| :=
  chapter9Clausen_one x

example (m : ℕ) (x : ℝ) (hm : 2 ≤ m) :
    chapter9Clausen m x = ∑' k : ℕ, chapter9ClausenTerm m x k :=
  chapter9Clausen_of_two_le m x hm

example (x : ℝ) : Summable (chapter9ClausenTerm 2 x) :=
  chapter9ClausenTerm_summable_of_two_le 2 x le_rfl

example (x : ℝ) (k : ℕ) :
    ‖chapter9ClausenTerm 2 x k‖ ≤ 1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
  chapter9ClausenTerm_norm_bound 2 x k

example (n : ℕ) (u : ℝ) :
    chapter9Entry13Integrand n u =
      u ^ n / 2 * (Real.cos (u / 2) / Real.sin (u / 2)) := rfl

end MathlibExtTest.Analysis.Ramanujan.Part1Ch9Entry13Bernoulligen
