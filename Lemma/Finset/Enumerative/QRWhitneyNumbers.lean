import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.QRWhitneyNumbers
open MetaMathlibExt
open QRWhitney


/--
[whitneyFirst_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneyFirst_zero_zero_eq
  {m r q : ℂ} [NeZero q] :
-- imply
  whitneyFirst m r q 0 0 = 1 := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneyFirst_zero_zero m r q

/--
[whitneyFirst_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneyFirst_zero_succ_eq
  {m r q : ℂ} [NeZero q]
  {k : ℕ} :
-- imply
  whitneyFirst m r q 0 (k + 1) = 0 := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneyFirst_zero_succ m r q k

/--
[whitneyFirst_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneyFirst_succ_zero_eq
  {m r q : ℂ} [NeZero q]
  {n : ℕ} :
-- imply
  whitneyFirst m r q (n + 1) 0 =
    (q ^ n)⁻¹ * (0 - (m * qBrack q n + r) * whitneyFirst m r q n 0) := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneyFirst_succ_zero m r q n

/--
[whitneyFirst_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneyFirst_succ_succ_eq
  {m r q : ℂ} [NeZero q]
  {n k : ℕ} :
-- imply
  whitneyFirst m r q (n + 1) (k + 1) =
    (q ^ n)⁻¹ *
    (whitneyFirst m r q n k -
    (m * qBrack q n + r) * whitneyFirst m r q n (k + 1)) := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneyFirst_succ_succ m r q n k

/--
[whitneySecond_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneySecond_zero_zero_eq
  {m r q : ℂ} :
-- imply
  whitneySecond m r q 0 0 = 1 := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneySecond_zero_zero m r q

/--
[whitneySecond_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneySecond_zero_succ_eq
  {m r q : ℂ}
  {k : ℕ} :
-- imply
  whitneySecond m r q 0 (k + 1) = 0 := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneySecond_zero_succ m r q k

/--
[whitneySecond_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneySecond_succ_zero_eq
  {m r q : ℂ}
  {n : ℕ} :
-- imply
  whitneySecond m r q (n + 1) 0 = r * whitneySecond m r q n 0 := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneySecond_succ_zero m r q n

/--
[whitneySecond_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneySecond_succ_succ_eq
  {m r q : ℂ}
  {n k : ℕ} :
-- imply
  whitneySecond m r q (n + 1) (k + 1) =
    q ^ k * whitneySecond m r q n k +
    (m * qBrack q (k + 1) + r) * whitneySecond m r q n (k + 1) := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneySecond_succ_succ m r q n k

/--
[whitneyFirst_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneyFirst_eq_zero_of_lt_eq
  {m r q : ℂ} [NeZero q]
  {n k : ℕ}
-- given
  (h : n < k) :
-- imply
  whitneyFirst m r q n k = 0 := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneyFirst_eq_zero_of_lt h

/--
[whitneySecond_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneySecond_eq_zero_of_lt_eq
  {m r q : ℂ}
  {n k : ℕ}
-- given
  (h : n < k) :
-- imply
  whitneySecond m r q n k = 0 := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneySecond_eq_zero_of_lt h

/--
[whitneyFirst_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneyFirst_succ_eq_eq
  {m r q : ℂ} [NeZero q]
  {n k : ℕ}
-- given
  (hk : 1 ≤ k) :
-- imply
  whitneyFirst m r q (n + 1) k =
    (q ^ n)⁻¹ *
    (whitneyFirst m r q n (k - 1) -
    (m * qBrack q n + r) * whitneyFirst m r q n k) := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneyFirst_succ_eq m r q n k hk

/--
[whitneySecond_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
private lemma whitneySecond_succ_eq_eq
  {m r q : ℂ}
  {n k : ℕ}
-- given
  (hk : 1 ≤ k) :
-- imply
  whitneySecond m r q (n + 1) k =
    q ^ (k - 1) * whitneySecond m r q n (k - 1) +
    (m * qBrack q k + r) * whitneySecond m r q n k := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneySecond_succ_eq m r q n k hk


-- created on 2026-10-20
