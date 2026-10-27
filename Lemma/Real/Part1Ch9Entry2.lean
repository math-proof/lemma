import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch9Entry2.Part8

open Ramanujan.Part1Ch9.Entry2

/--
[Part1Ch9Entry2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry2.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry2_is
-- given
  (r : ℕ)
  (a x : ℝ)
  (hr : 2 ≤ r)
  (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
  (hxLower : 0 < x)
  (hxUpper : x < Real.pi) :
-- imply
  Summable (chapter9Entry2ConstantTerm r a) ∧
    ((Even r ∧
        (∀ k ∈ Finset.range (r / 2),
          Summable (chapter9Entry2ConstantTerm (r - 2 * k) a)) ∧
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ k ∈ Finset.range N, chapter9Entry2CosineTerm r a x k)
          Filter.atTop
          (nhds
            ((∑ k ∈ Finset.range (r / 2),
                (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 2 * k) a *
                  x ^ (2 * k) / ((2 * k).factorial : ℝ)) +
              (-1 : ℝ) ^ (r / 2) * Real.pi * x ^ (r - 1) /
                (2 * ((r - 1).factorial : ℝ))))) ∨
      (Odd r ∧
        (∀ k ∈ Finset.range ((r - 1) / 2),
          Summable (chapter9Entry2ConstantTerm (r - 1 - 2 * k) a)) ∧
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ k ∈ Finset.range N, chapter9Entry2SineTerm r a x k)
          Filter.atTop
          (nhds
            ((∑ k ∈ Finset.range ((r - 1) / 2),
                (-1 : ℝ) ^ k * chapter9Entry2Constant (r - 1 - 2 * k) a *
                  x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) +
              (-1 : ℝ) ^ ((r - 1) / 2) * Real.pi * x ^ (r - 1) /
                (2 * ((r - 1).factorial : ℝ)))))) := by
-- proof
  apply Ramanujan.Part1Ch9.Entry2.ramanujan_part1_ch9_entry2 r a x hr ha hxLower hxUpper

-- created on 2026-10-10
