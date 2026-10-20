import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SulankeNumber
open MetaMathlibExt


/--
[sulankeB_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
private lemma sulankeB_zero_eq
  :
-- imply
  sulankeB 0 0 = 1 := by
-- proof
  apply MetaMathlibExt.sulankeB_zero

/--
[sulankeB_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
private lemma sulankeB_zero_succ_eq
  {i : ℕ} :
-- imply
  sulankeB 0 (i + 1) = 0 := by
-- proof
  apply MetaMathlibExt.sulankeB_zero_succ i

/--
[sulankeA_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
private lemma sulankeA_zero_eq
  {i : ℕ} :
-- imply
  sulankeA 0 i = 0 := by
-- proof
  apply MetaMathlibExt.sulankeA_zero i

/--
[sulankeA_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
private lemma sulankeA_succ_zero_eq
  {k : ℕ} :
-- imply
  sulankeA (k + 1) 0 = sulankeB k 0 := by
-- proof
  apply MetaMathlibExt.sulankeA_succ_zero k

/--
[sulankeA_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
private lemma sulankeA_succ_succ_eq
  {k n : ℕ} :
-- imply
  sulankeA (k + 1) (n + 1) = sulankeB k (n + 1) + 2 * sulankeB k n := by
-- proof
  apply MetaMathlibExt.sulankeA_succ_succ k n

/--
[sulankeB_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
private lemma sulankeB_succ_zero_eq
  {k : ℕ} :
-- imply
  sulankeB (k + 1) 0 = sulankeA (k + 1) 0 := by
-- proof
  apply MetaMathlibExt.sulankeB_succ_zero k

/--
[sulankeB_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
private lemma sulankeB_succ_succ_eq
  {k n : ℕ} :
-- imply
  sulankeB (k + 1) (n + 1) = sulankeA (k + 1) (n + 1) + sulankeA (k + 1) n := by
-- proof
  apply MetaMathlibExt.sulankeB_succ_succ k n

/--
[sulankeB_eq_zero_of_two_mul_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
private lemma sulankeB_eq_zero_of_two_mul_lt_eq
  {k : ℕ} :
-- imply
  ∀ i : ℕ, 2 * k < i → sulankeB k i = 0 := by
-- proof
  apply MetaMathlibExt.sulankeB_eq_zero_of_two_mul_lt k

/--
[sulankeA_eq_zero_of_two_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean)
-/
@[path]
private lemma sulankeA_eq_zero_of_two_mul_le_eq
  {k : ℕ} :
-- imply
  ∀ i : ℕ, 2 * k ≤ i → sulankeA k i = 0 := by
-- proof
  apply MetaMathlibExt.sulankeA_eq_zero_of_two_mul_le k


-- created on 2026-10-20
