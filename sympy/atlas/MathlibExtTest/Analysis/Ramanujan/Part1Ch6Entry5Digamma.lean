/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch6Entry5Digamma.lean -/


import sympy.atlas.Analysis.Ramanujan.Part1Ch6Entry5Digamma

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 5 API checks

The first terms of the factorial series, its convergence and functional equation at `x = 1`, and
the first asymptotic orders.
-/

namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch6Entry5Digamma

open MathlibExt.Analysis.Ramanujan.Part1Ch6.Entry5Digamma

open Asymptotics Filter

example (x : ℝ) : chapter6Section13ExampleCTerm x 0 = 1 / (x + 1) := by simp

example : chapter6Section13ExampleCTerm 1 1 = -1 / 6 := by
  rw [chapter6Section13ExampleCTerm_succ]
  norm_num

example : Summable (chapter6Section13ExampleCTerm 1) :=
  summable_chapter6Section13ExampleCTerm 1 one_pos

example : chapter6Section13ExampleCSum 1 = 1 / 2 - chapter6Section13ExampleCSum 2 / 2 := by
  have := chapter6Section13ExampleCSum_eq 1 one_pos
  norm_num at this
  exact this

example : ∀ᶠ x : ℝ in atTop, 0 < x ∧ Summable (chapter6Section13ExampleCTerm x) :=
  ramanujan_part1_ch6_entry5_digamma.1

-- `C(x) = 1 / x + O(1 / x²)`, since `Nat.bell 1 = 1`.
example : (fun x : ℝ => chapter6Section13ExampleCSum x - 1 / x) =O[atTop]
    (fun x : ℝ => 1 / x ^ 2) := by
  have hbell : (1 : ℕ).bell = 1 := Nat.bell_one
  have h := ramanujan_part1_ch6_entry5_digamma.2 1
  simp only [Finset.sum_range_one, pow_zero, one_mul, zero_add, pow_one, hbell,
    Nat.cast_one] at h
  exact h

-- `C(x) = 1 / x - 2 / x² + O(1 / x³)`, since `Nat.bell 2 = 2`.
example : (fun x : ℝ => chapter6Section13ExampleCSum x - (1 / x - 2 / x ^ 2)) =O[atTop]
    (fun x : ℝ => 1 / x ^ 3) := by
  simpa [Finset.sum_range_succ, sub_eq_add_neg, neg_div] using
    isBigO_chapter6Section13ExampleCSum_sub_sum_bell 2

end MathlibExtTest.Analysis.Ramanujan.Part1Ch6Entry5Digamma
