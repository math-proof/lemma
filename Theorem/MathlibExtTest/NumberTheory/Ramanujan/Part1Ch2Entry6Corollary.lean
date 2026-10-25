/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch2Entry6Corollary.lean -/


import Def.NumberTheory.Ramanujan.Part1Ch2Entry6Corollary
import Lemma.Nat.Ramanujan.Part1Ch2Entry6Corollary
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Corollary to Entry 6 API checks

Values of `A` from its simp lemmas, and the corollary at `r = 2`.
-/


namespace MathlibExtTest.NumberTheory.Ramanujan.Part1Ch2Entry6Corollary

open MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6Corollary

example : A 1 = 1 ∧ A 2 = 4 ∧ A 3 = 13 := by simp

example (k : ℕ) : 2 * A k + 1 = 3 ^ k := A_two_mul_add_one k

-- `r = 2`: `1 + 1/2 + 1/3 + 1/4 = 2 + 2 / (3 ^ 3 - 3)`.
example : ∑ j ∈ Finset.Icc (1 : ℕ) 4, (1 : ℚ) / j = 2 + 2 * (1 / 24) := by
  rw [show 4 = A 2 by simp, ramanujan_part1_ch2_entry6_corollary 2 two_pos]
  norm_num [Finset.sum_singleton]

end MathlibExtTest.NumberTheory.Ramanujan.Part1Ch2Entry6Corollary
