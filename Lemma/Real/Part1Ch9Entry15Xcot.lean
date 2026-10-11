import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch9Entry15Xcot

open Ramanujan.Part1Ch9.Entry15Xcot

/--
[Part1Ch9Entry15Xcot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry15Xcot.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry15_xcot_eq
-- given
  (n : ℕ) :
-- imply
  (∀ k : ℕ, k ≤ n → ∀ y : ℝ, 0 < y → y < Real.pi →
      IntervalIntegrable (fun u : ℝ => u ^ k * (Real.cos u / Real.sin u))
        MeasureTheory.volume (Real.pi / 4) y) ∧
    ∀ x : ℝ, 0 < x → x < Real.pi / 2 →
      (2 : ℝ) ^ n * chapter9CotPrimitive n (Real.pi / 2 - x) =
        (∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k) *
            (chapter9CotPrimitive k (2 * x) -
              (2 : ℝ) ^ k * chapter9CotPrimitive k x)) -
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ k * (n.choose k : ℝ) * Real.pi ^ (n - k) *
            chapter9CotPrimitive k (Real.pi / 2) := by
-- proof
  apply Ramanujan.Part1Ch9.Entry15Xcot.ramanujan_part1_ch9_entry15_xcot n

-- created on 2026-10-10
