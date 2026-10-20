import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.EngelExpansion
open EngelExpansion


/--
[negRem_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma negRem_lt_eq
  {n k : ℕ}
-- given
  (hk : k ≠ 0) :
-- imply
  negRem n k < k := by
-- proof
  apply EngelExpansion.negRem_lt hk

/--
[negRem_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma negRem_eq_iff_eq
  {n k u : ℕ}
-- given
  (hk : k ≠ 0) :
-- imply
  negRem n k = u ↔ u < k ∧ k ∣ n + u := by
-- proof
  apply EngelExpansion.negRem_eq_iff hk

/--
[traj_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma traj_zero_eq
  {n a : ℕ} :
-- imply
  traj n a 0 = a := by
-- proof
  apply EngelExpansion.traj_zero n a

/--
[traj_succ_of_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma traj_succ_of_eq_zero_eq
  {n a j : ℕ}
-- given
  (h : traj n a j = 0) :
-- imply
  traj n a (j + 1) = 0 := by
-- proof
  apply EngelExpansion.traj_succ_of_eq_zero h

/--
[traj_succ_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma traj_succ_of_ne_zero_eq
  {n a j : ℕ}
-- given
  (h : traj n a j ≠ 0) :
-- imply
  traj n a (j + 1) = negRem n (traj n a j) := by
-- proof
  apply EngelExpansion.traj_succ_of_ne_zero h

/--
[traj_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma traj_one_eq
  {n t : ℕ}
-- given
  (ht : t ≠ 0) :
-- imply
  traj n t 1 = negRem n t := by
-- proof
  apply EngelExpansion.traj_one ht

/--
[exists_traj_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma exists_traj_eq_zero_eq
  {n a : ℕ} :
-- imply
  ∃ i ≤ a + 1, traj n a i = 0 := by
-- proof
  apply EngelExpansion.exists_traj_eq_zero n a

/--
[exists_traj_eq_zero_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma exists_traj_eq_zero_pos_eq
  {n a : ℕ} :
-- imply
  ∃ j ≥ 1, traj n a j = 0 := by
-- proof
  apply EngelExpansion.exists_traj_eq_zero_pos n a

/--
[length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma length_pos_eq
  {n a : ℕ} :
-- imply
  1 ≤ length n a := by
-- proof
  apply EngelExpansion.length_pos n a

/--
[traj_length_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma traj_length_eq_zero_eq
  {n a : ℕ} :
-- imply
  traj n a (length n a) = 0 := by
-- proof
  apply EngelExpansion.traj_length_eq_zero n a

/--
[length_le_of_traj_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma length_le_of_traj_eq_zero_eq
  {n a j : ℕ}
-- given
  (hj : 1 ≤ j)
  (h : traj n a j = 0) :
-- imply
  length n a ≤ j := by
-- proof
  apply EngelExpansion.length_le_of_traj_eq_zero hj h

/--
[traj_ne_zero_of_lt_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma traj_ne_zero_of_lt_length_eq
  {n a j : ℕ}
-- given
  (hj : 1 ≤ j)
  (hlt : j < length n a) :
-- imply
  traj n a j ≠ 0 := by
-- proof
  apply EngelExpansion.traj_ne_zero_of_lt_length hj hlt

/--
[length_le_maxLength](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma length_le_maxLength_eq
  {n a : ℕ}
-- given
  (ha : a ∈ Finset.Icc 1 n) :
-- imply
  length n a ≤ maxLength n := by
-- proof
  apply EngelExpansion.length_le_maxLength ha

/--
[maxLength_le_of_forall](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean)
-/
@[path]
private lemma maxLength_le_of_forall_eq
  {n L : ℕ}
-- given
  (h : ∀ a ∈ Finset.Icc 1 n, length n a ≤ L) :
-- imply
  maxLength n ≤ L := by
-- proof
  apply EngelExpansion.maxLength_le_of_forall h


-- created on 2026-10-20
