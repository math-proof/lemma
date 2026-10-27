import Mathlib.Tactic
import Notation.Data.Int.Integers
export Int (fract sign)


class SubSelf (Z : Type*) [Zero Z] extends Sub Z where
  sub_self (a : Z) : a - a = 0

class IntegerRing (Z : Type) extends Semiring Z, LinearOrder Z, IsStrictOrderedRing Z, SubSelf Z, Div Z, Mod Z, CommMagma Z, MulDivCancelClass Z, CommMonoidWithZero Z where
  succ_le_of_lt {a b : Z} : a < b → a + 1 ≤ b
  lt_of_succ_le {a b : Z} : a + 1 ≤ b → a < b
  lt_succ_of_le {a b : Z} : a ≤ b → a < b + 1
  le_pred_of_lt {a b : Z} : a < b → a ≤ b - 1
  add_sub_cancel (a b : Z) : a + b - b = a
  sub_add_cancel {a b : Z} : a ≤ b → b - a + a = b
  sub_le_sub_left {a b c : Z} : a ≤ b → c - b ≤ c - a
  sub_pred {n d : Z} (h : d > 0) : n - (d - 1) = n + 1 - d
  div_add_mod (n d : Z) : d * (n / d) + n % d = n
  mod_lt {d : Z} (h : d > 0) (n : Z) : n % d < d
  pred_le (n : Z) : n - 1 ≤ n
  pred_lt {n : Z} : n ≠ 0 → n - 1 < n
  lt_succ_self (n : Z) : n < n + 1
  add_mul_mod_self_left (a b c : Z) : (a + b * c) % b = a % b
  add_mul_mod_self_right (a b c : Z) : (a + b * c) % c = a % c
  add_div_of_dvd_left {a b c : Z} : c ∣ b → (a + b) / c = a / c + b / c
  add_div_of_dvd_right {a b c : Z} : c ∣ a → (a + b) / c = a / c + b / c
  div_mul_cancel {a b : Z} : b ∣ a → a / b * b = a
  mul_div_assoc (a : Z) : (c ∣ b) → a * b / c = a * (b / c)
  div_one (n : Z) : n / 1 = n
  div_eq_zero_of_lt {a b : Z} : (a ≥ 0) → (a < b) → a / b = 0
  zero_mod (n : Z) : 0 % n = 0
  div_self {n : Z} : n ≠ 0 → n / n = 1
  div_zero (n : Z) : n / 0 = 0
  even_iff {n : Z} : Even n ↔ n % 2 = 0
  odd_iff {n : Z} : Odd n ↔ n % 2 = 1
  mod_two_ne_one {n : Z} : n % 2 ≠ 1 ↔ n % 2 = 0
  mod_mul {k m n : Z}: k % (m * n) % n = k % n

