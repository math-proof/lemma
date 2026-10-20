import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry6
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry6


/--
[A_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma A_zero_eq
  {n : ℕ} :
-- imply
  A n 0 = n := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6.A_zero n

/--
[A_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma A_succ_eq
  {n k : ℕ} :
-- imply
  A n (k + 1) = 3 * A n k + 1 := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6.A_succ n k

/--
[A_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma A_ge_eq
  {n k : ℕ} :
-- imply
  n ≤ A n k := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6.A_ge n k

/--
[ramanujan_part1_ch2_entry6_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry6_general_eq
  {n r : ℕ} :
-- imply
  ∑ j ∈ Finset.Icc (n + 1) (A n r), (1 : ℚ) / ((j : ℕ) : ℚ)
    = (r : ℚ) + 2 * ∑ k ∈ Finset.range r, (((r - k : ℕ)) : ℚ) *
    ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k),
    (1 : ℚ) / ((3 * ((j : ℕ) : ℚ)) ^ 3 - 3 * ((j : ℕ) : ℚ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6.ramanujan_part1_ch2_entry6_general n r

/--
[ramanujan_part1_ch2_entry6](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry6_eq
  {n r : ℕ}
-- given
  (hr : 0 < r) :
-- imply
  ∑ j ∈ Finset.Icc (n + 1) (A n r), (1 : ℚ) / (j : ℚ) =
    (r : ℚ) + 2 * ∑ k ∈ Finset.range r, ((r - k : ℕ) : ℚ) *
    ∑ j ∈ Finset.Icc (if k = 0 then 1 else A n (k - 1) + 1) (A n k), (1 : ℚ) /
    ((3 * (j : ℚ)) ^ 3 - 3 * (j : ℚ)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry6.ramanujan_part1_ch2_entry6 n r hr


-- created on 2026-10-20
