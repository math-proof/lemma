/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
# Polygonal numbers

This file formalizes the polygonal-number family from Zhi-Wei Sun's
"On universal sums of polygonal numbers" (Sci. China Math. 58 (2015), 1367--1396).

The source defines, for `m = 3, 4, ...` and `n = 0, 1, 2, ...`,
`p_m(n) = (m - 2) * C(n, 2) + n`.

The source's geometric polygonal interpretation assumes `3 ≤ s`.
The Lean definition below is the total natural-number extension of that
binomial formula to all `s : ℕ`, using `Nat.choose` so no unintended
truncated-subtraction semantics enter the definition itself.
-/

namespace Nat

/-- Doubling identity underlying the square, pentagonal, and hexagonal forms. -/
private theorem two_choose_add (n : ℕ) : 2 * (Nat.choose n 2) + n = n ^ 2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hpascal : Nat.choose (n + 1) 2 = Nat.choose n 2 + n := by
      simpa [Nat.choose_one_right, Nat.add_comm] using Nat.choose_succ_succ n 1
    have hsq : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    omega

/-- Polygonal-number family: `polygonalNumber s n = (s - 2) * C(n, 2) + n`.

The source's polygonal interpretation assumes `3 ≤ s`; this definition is the
total natural extension to all `s : ℕ`. -/
def polygonalNumber (s n : ℕ) : ℕ := (s - 2) * Nat.choose n 2 + n

/-- Total-extension initial value at `0`; the source claims this only for `3 ≤ s`. -/
@[simp] theorem polygonalNumber_zero (s : ℕ) : polygonalNumber s 0 = 0 := by
  have h : Nat.choose 0 2 = 0 := by decide
  simp [polygonalNumber, h]

/-- Total-extension initial value at `1`; the source claims this only for `3 ≤ s`. -/
@[simp] theorem polygonalNumber_one (s : ℕ) : polygonalNumber s 1 = 1 := by
  have h : Nat.choose 1 2 = 0 := by decide
  simp only [polygonalNumber, h]
  simp

/-- Source initial value at `2`: `p_m(2) = m` for `3 ≤ s`. -/
theorem polygonalNumber_at_two (s : ℕ) (hs : 3 ≤ s) : polygonalNumber s 2 = s := by
  have hc : Nat.choose 2 2 = 1 := by decide
  simp only [polygonalNumber, hc]
  omega

/-- Source initial value at `3`: `p_m(3) = 3 * m - 3` for `3 ≤ s`. -/
theorem polygonalNumber_at_three (s : ℕ) (hs : 3 ≤ s) :
    polygonalNumber s 3 = 3 * s - 3 := by
  have hc : Nat.choose 3 2 = 3 := by decide
  simp only [polygonalNumber, hc]
  omega

/-- Source initial value at `4`: `p_m(4) = 6 * m - 8` for `3 ≤ s`. -/
theorem polygonalNumber_at_four (s : ℕ) (hs : 3 ≤ s) :
    polygonalNumber s 4 = 6 * s - 8 := by
  have hc : Nat.choose 4 2 = 6 := by decide
  simp [polygonalNumber, hc]
  omega

/-- Triangular specialization `p_3(n) = n * (n + 1) / 2`. -/
theorem polygonalNumber_three (n : ℕ) :
    polygonalNumber 3 n = n * (n + 1) / 2 := by
  have h4 : 2 * (Nat.choose n 2) + n = n ^ 2 := two_choose_add n
  have hmul : n * (n + 1) = n ^ 2 + n := by ring
  simp [polygonalNumber]
  omega

/-- Square specialization `p_4(n) = n ^ 2`. -/
theorem polygonalNumber_four (n : ℕ) : polygonalNumber 4 n = n ^ 2 := by
  simpa [polygonalNumber] using two_choose_add n

/-- Pentagonal specialization `p_5(n) = (3 * n ^ 2 - n) / 2`. -/
theorem polygonalNumber_five (n : ℕ) :
    polygonalNumber 5 n = (3 * n ^ 2 - n) / 2 := by
  have h4 : 2 * (Nat.choose n 2) + n = n ^ 2 := two_choose_add n
  simp [polygonalNumber]
  omega

/-- Hexagonal specialization `p_6(n) = 2 * n ^ 2 - n`. -/
theorem polygonalNumber_six (n : ℕ) :
    polygonalNumber 6 n = 2 * n ^ 2 - n := by
  have h4 : 2 * (Nat.choose n 2) + n = n ^ 2 := two_choose_add n
  simp [polygonalNumber]
  omega

end Nat
