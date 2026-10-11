import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch9Entry1Logratio

open Ramanujan.Part1Ch9.Entry1Logratio

/--
[Part1Ch9Entry1Logratio](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry1Logratio.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry1_logratio_is
-- given
  (r : ℕ)
  (a x : ℝ)
  (hr : 0 < r)
  (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
  (hx : |x| < Real.pi) :
-- imply
  Summable (chapter9Entry1ConstantTerm r a) ∧
    ((Odd r ∧
        (∀ k ∈ Finset.range ((r - 1) / 2 + 1),
          Summable (chapter9Entry1ConstantTerm (r - 2 * k) a)) ∧
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ k ∈ Finset.range N, chapter9Entry1CosineTerm r a x k)
          Filter.atTop
          (nhds (∑ k ∈ Finset.range ((r - 1) / 2 + 1),
            (-1 : ℝ) ^ k * chapter9Entry1Constant (r - 2 * k) a *
              x ^ (2 * k) / ((2 * k).factorial : ℝ)))) ∨
      (Even r ∧
        (∀ k ∈ Finset.range (r / 2),
          Summable (chapter9Entry1ConstantTerm (r - 2 * k - 1) a)) ∧
        Filter.Tendsto
          (fun N : ℕ =>
            ∑ k ∈ Finset.range N, chapter9Entry1SineTerm r a x k)
          Filter.atTop
          (nhds (∑ k ∈ Finset.range (r / 2),
            (-1 : ℝ) ^ k * chapter9Entry1Constant (r - 2 * k - 1) a *
              x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ))))) := by
-- proof
  apply Ramanujan.Part1Ch9.Entry1Logratio.ramanujan_part1_ch9_entry1_logratio r a x hr ha hx

-- created on 2026-10-10
