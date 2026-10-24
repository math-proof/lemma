/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch2Entry6.lean -/


import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry6
import Lemma.Nat.Ramanujan.Part1Ch2Entry6
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 6 API checks

Values of `A` from its recurrence, the `n = 0` and `r = 0` boundaries, and Entry 6 at
`n = 1`, `r = 1`.
-/

namespace MathlibExtTest.NumberTheory.Ramanujan.Part1Ch2Entry6

open MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6

example : A 1 1 = 4 ∧ A 1 2 = 13 ∧ A 2 1 = 7 := by decide

-- `n = 0`: `A 0 k = (3 ^ k - 1) / 2`.
example : A 0 0 = 0 ∧ A 0 1 = 1 ∧ A 0 2 = 4 := by decide

example (n : ℕ) : A n 0 = n := by simp

example (n : ℕ) : A n 2 = 9 * n + 4 := by
  rw [A_succ, A_succ, A_zero]
  omega

example (n k : ℕ) : n ≤ A n (k + 1) := A_ge n (k + 1)

-- `r = 0`: the harmonic block `Finset.Icc (n + 1) n` is empty.
example (n : ℕ) : ∑ j ∈ Finset.Icc (n + 1) (A n 0), (1 : ℚ) / j = 0 := by
  rw [ramanujan_part1_ch2_entry6_general n 0]
  simp

-- `n = 0`, `r = 1`: the inner sum over `Finset.Icc 1 (A 0 0)` is empty.
example : ∑ j ∈ Finset.Icc (1 : ℕ) 1, (1 : ℚ) / j = 1 := by
  rw [show Finset.Icc (1 : ℕ) 1 = Finset.Icc (0 + 1) (A 0 1) by decide,
    ramanujan_part1_ch2_entry6 0 1 one_pos]
  norm_num

-- `n = 1`, `r = 1`: `1/2 + 1/3 + 1/4 = 1 + 2 / (3 ^ 3 - 3)`.
example : ∑ j ∈ Finset.Icc (2 : ℕ) 4, (1 : ℚ) / j = 1 + 2 * (1 / 24) := by
  rw [show Finset.Icc (2 : ℕ) 4 = Finset.Icc (1 + 1) (A 1 1) by decide,
    ramanujan_part1_ch2_entry6 1 1 one_pos]
  norm_num [Finset.sum_singleton]

end MathlibExtTest.NumberTheory.Ramanujan.Part1Ch2Entry6
