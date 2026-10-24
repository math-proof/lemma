import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.QRWhitneyNumbers
open MetaMathlibExt
open QRWhitney


namespace MetaMathlibExt.QRWhitney

/--
[whitneyFirst_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneyFirst_zero_zero
  {m r q : ℂ} [NeZero q] :
-- imply
  whitneyFirst m r q 0 0 = 1 :=
-- proof
  rfl

end MetaMathlibExt.QRWhitney

namespace MetaMathlibExt.QRWhitney

/--
[whitneyFirst_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneyFirst_zero_succ
  {m r q : ℂ} [NeZero q]
  {k : ℕ} :
-- imply
  whitneyFirst m r q 0 (k + 1) = 0 :=
-- proof
  rfl

end MetaMathlibExt.QRWhitney

namespace MetaMathlibExt.QRWhitney

/--
[whitneyFirst_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneyFirst_succ_zero
  {m r q : ℂ} [NeZero q]
  {n : ℕ} :
-- imply
  whitneyFirst m r q (n + 1) 0 =
    (q ^ n)⁻¹ * (0 - (m * qBrack q n + r) * whitneyFirst m r q n 0) :=
-- proof
  rfl

end MetaMathlibExt.QRWhitney

namespace MetaMathlibExt.QRWhitney

/--
[whitneyFirst_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneyFirst_succ_succ
  {m r q : ℂ} [NeZero q]
  {n k : ℕ} :
-- imply
  whitneyFirst m r q (n + 1) (k + 1) =
    (q ^ n)⁻¹ *
    (whitneyFirst m r q n k -
    (m * qBrack q n + r) * whitneyFirst m r q n (k + 1)) :=
-- proof
  rfl

end MetaMathlibExt.QRWhitney

namespace MetaMathlibExt.QRWhitney

/--
[whitneySecond_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneySecond_zero_zero
  {m r q : ℂ} :
-- imply
  whitneySecond m r q 0 0 = 1 :=
-- proof
  rfl

end MetaMathlibExt.QRWhitney

namespace MetaMathlibExt.QRWhitney

/--
[whitneySecond_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneySecond_zero_succ
  {m r q : ℂ}
  {k : ℕ} :
-- imply
  whitneySecond m r q 0 (k + 1) = 0 :=
-- proof
  rfl

end MetaMathlibExt.QRWhitney

namespace MetaMathlibExt.QRWhitney

/--
[whitneySecond_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneySecond_succ_zero
  {m r q : ℂ}
  {n : ℕ} :
-- imply
  whitneySecond m r q (n + 1) 0 = r * whitneySecond m r q n 0 :=
-- proof
  rfl

end MetaMathlibExt.QRWhitney

namespace MetaMathlibExt.QRWhitney

/--
[whitneySecond_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneySecond_succ_succ
  {m r q : ℂ}
  {n k : ℕ} :
-- imply
  whitneySecond m r q (n + 1) (k + 1) =
    q ^ k * whitneySecond m r q n k +
    (m * qBrack q (k + 1) + r) * whitneySecond m r q n (k + 1) :=
-- proof
  rfl

end MetaMathlibExt.QRWhitney

namespace MetaMathlibExt.QRWhitney

/--
[whitneyFirst_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneyFirst_eq_zero_of_lt
  {m r q : ℂ} [NeZero q]
  {n k : ℕ}
-- given
  (h : n < k) :
-- imply
  whitneyFirst m r q n k = 0 := by
-- proof
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k => exact whitneyFirst_zero_succ m r q k
  | succ n ih =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k =>
      have h1 : n < k := Nat.lt_of_succ_lt_succ h
      have h2 : n < k + 1 := Nat.lt_trans h1 (Nat.lt_succ_self k)
      rw [whitneyFirst_succ_succ, ih h1, ih h2, mul_zero, sub_zero, mul_zero]

end MetaMathlibExt.QRWhitney

namespace MetaMathlibExt.QRWhitney

/--
[whitneySecond_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneySecond_eq_zero_of_lt
  {m r q : ℂ}
  {n k : ℕ}
-- given
  (h : n < k) :
-- imply
  whitneySecond m r q n k = 0 := by
-- proof
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k => exact whitneySecond_zero_succ m r q k
  | succ n ih =>
    cases k with
    | zero => exact absurd h (by omega)
    | succ k =>
      have h1 : n < k := Nat.lt_of_succ_lt_succ h
      have h2 : n < k + 1 := Nat.lt_trans h1 (Nat.lt_succ_self k)
      rw [whitneySecond_succ_succ, ih h1, ih h2, mul_zero, mul_zero, add_zero]

end MetaMathlibExt.QRWhitney

namespace MetaMathlibExt.QRWhitney

/--
[whitneyFirst_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneyFirst_succ_eq
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
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h : j + 1 - 1 = j := Nat.add_sub_cancel j 1
  rw [h]
  exact whitneyFirst_succ_succ m r q n j

end MetaMathlibExt.QRWhitney

namespace MetaMathlibExt.QRWhitney

/--
[whitneySecond_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRWhitneyNumbers.lean)
-/
@[path]
lemma whitneySecond_succ_eq
  {m r q : ℂ}
  {n k : ℕ}
-- given
  (hk : 1 ≤ k) :
-- imply
  whitneySecond m r q (n + 1) k =
    q ^ (k - 1) * whitneySecond m r q n (k - 1) +
    (m * qBrack q k + r) * whitneySecond m r q n k := by
-- proof
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h : j + 1 - 1 = j := Nat.add_sub_cancel j 1
  rw [h]
  exact whitneySecond_succ_succ m r q n j

end MetaMathlibExt.QRWhitney


-- created on 2026-10-20
-- updated on 2026-10-23
