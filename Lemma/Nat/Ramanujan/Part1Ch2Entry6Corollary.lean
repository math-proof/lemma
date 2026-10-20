import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry6Corollary
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry6Corollary


/--
[A_two_mul_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6Corollary.lean)
-/
@[path]
private lemma A_two_mul_add_one_eq
  {k : ℕ} :
-- imply
  2 * A k + 1 = 3 ^ k := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6Corollary.A_two_mul_add_one k

/--
[A_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6Corollary.lean)
-/
@[path]
private lemma A_zero_eq
  :
-- imply
  A 0 = 0 := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6Corollary.A_zero

/--
[A_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6Corollary.lean)
-/
@[path]
private lemma A_succ_eq
  {k : ℕ} :
-- imply
  A (k + 1) = 3 * A k + 1 := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6Corollary.A_succ k

/--
[ramanujan_part1_ch2_entry6_corollary_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6Corollary.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry6_corollary_general_eq
  {r : ℕ} :
-- imply
  ∑ j ∈ Finset.Icc 1 (A r), (1 : ℚ) / (j : ℚ) = (r : ℚ) + 2 * ∑ k ∈ Finset.Icc 1 (r - 1),
    ((r - k : ℕ) : ℚ) *
    ∑ j ∈ Finset.Icc (A (k - 1) + 1) (A k), (1 : ℚ) / ((3 * (j : ℚ)) ^ 3 - 3 * (j : ℚ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6Corollary.ramanujan_part1_ch2_entry6_corollary_general r

/--
[ramanujan_part1_ch2_entry6_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6Corollary.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry6_corollary_eq
  {r : ℕ}
-- given
  (hr : 0 < r) :
-- imply
  ∑ j ∈ Finset.Icc 1 (A r), (1 : ℚ) / (j : ℚ) = (r : ℚ) + 2 * ∑ k ∈ Finset.Icc 1 (r - 1),
    ((r - k : ℕ) : ℚ) *
    ∑ j ∈ Finset.Icc (A (k - 1) + 1) (A k), (1 : ℚ) / ((3 * (j : ℚ)) ^ 3 - 3 * (j : ℚ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6Corollary.ramanujan_part1_ch2_entry6_corollary r hr


-- created on 2026-10-20
