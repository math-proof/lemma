import Mathlib.Tactic

export Int (fract sign)
notation:max n "is" "even" => Even n
notation:max n "isn't" "even" => ¬Even n
notation:max n "is" "odd" => Odd n
notation:max n "isn't" "odd" => ¬Odd n
infixl:70 "//" => Int.fdiv

class SubSelf (Z : Type*) [Zero Z] extends Sub Z where
  sub_self (a : Z) : a - a = 0

class IntegerRing (Z : Type) extends Semiring Z, LinearOrder Z, IsStrictOrderedRing Z, SubSelf Z, Div Z, Mod Z, CommMagma Z, MulDivCancelClass Z, CommMonoidWithZero Z where
  succ_le_of_lt {a b : Z} : a < b → a + 1 ≤ b
  lt_of_succ_le {a b : Z} : a + 1 ≤ b → a < b
  lt_succ_of_le {a b : Z} : a ≤ b → a < b + 1
  le_pred_of_lt {a b : Z} : a < b → a ≤ b - 1
  add_sub_cancel (a b : Z) : a + b - b = a
  sub_add_cancel {a b : Z} : a ≤ b → b - a + a = b
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

instance : IntegerRing ℕ where
  succ_le_of_lt := Nat.succ_le_of_lt
  lt_of_succ_le := Nat.lt_of_succ_le
  lt_succ_of_le := Nat.lt_succ_of_le
  le_pred_of_lt := Nat.le_pred_of_lt
  add_sub_cancel := Nat.add_sub_cancel
  sub_add_cancel := by
    intro a b
    apply Nat.sub_add_cancel
  div_add_mod := by
    intro n d
    apply Nat.div_add_mod n d
  mod_lt {d : ℕ} (h : d > 0) (n : ℕ) := Nat.mod_lt n h
  pred_le := Nat.pred_le
  pred_lt := Nat.pred_lt
  lt_succ_self := Nat.lt_succ_self
  add_mul_mod_self_left := Nat.add_mul_mod_self_left
  add_mul_mod_self_right := Nat.add_mul_mod_self_right
  mul_comm := Nat.mul_comm
  add_div_of_dvd_left {a b c : ℕ} (h : c ∣ b) := Nat.add_div_of_dvd_left h
  add_div_of_dvd_right {a b c : ℕ} (h : c ∣ a) := Nat.add_div_of_dvd_right h
  div_mul_cancel := Nat.div_mul_cancel
  mul_div_assoc := Nat.mul_div_assoc
  div_one := Nat.div_one
  div_eq_zero_of_lt := by simp_all
  sub_self := Nat.sub_self
  zero_mod := Nat.zero_mod
  div_self {n : ℕ} (h : n ≠ 0) := Nat.div_self (by omega)
  div_zero := Nat.div_zero
  even_iff := Nat.even_iff
  odd_iff := Nat.odd_iff
  mod_two_ne_one := Nat.mod_two_not_eq_one
  mod_mul := by simp

instance : IntegerRing ℤ where
  succ_le_of_lt := Int.add_one_le_of_lt
  lt_of_succ_le := Int.lt_of_add_one_le
  lt_succ_of_le := Int.lt_add_one_of_le
  le_pred_of_lt := Int.le_sub_one_of_lt
  add_sub_cancel := Int.add_sub_cancel
  sub_add_cancel := by
    intro a b h
    apply Int.sub_add_cancel
  div_add_mod := by
    intro n d
    rw [Int.add_comm]
    apply Int.emod_add_mul_ediv
  mod_lt {d : ℤ} (h : d > 0) (n : ℤ) := Int.emod_lt_of_pos n h
  pred_le := by simp
  pred_lt := by simp
  lt_succ_self (n : ℤ) := by simp
  add_mul_mod_self_left := Int.add_mul_emod_self_left
  add_mul_mod_self_right := by
    intros
    apply Int.add_mul_emod_self_right
  mul_comm := Int.mul_comm
  add_div_of_dvd_left {a b c : ℤ} (h : c ∣ b) := by
    rw [add_comm]
    rw [add_comm (a := a / c)]
    apply Int.add_ediv_of_dvd_left h
  add_div_of_dvd_right {a b c : ℤ} (h : c ∣ a) := by
    rw [add_comm]
    rw [add_comm (a := a / c)]
    apply Int.add_ediv_of_dvd_right h
  div_mul_cancel := Int.ediv_mul_cancel
  mul_div_assoc := by
    intros
    apply Int.mul_ediv_assoc
    assumption
  div_one := Int.ediv_one
  div_eq_zero_of_lt := Int.ediv_eq_zero_of_lt
  sub_self := Int.sub_self
  zero_mod := Int.zero_emod
  div_self := Int.ediv_self
  div_zero := Int.ediv_zero
  even_iff := Int.even_iff
  odd_iff := Int.odd_iff
  mod_two_ne_one := Int.emod_two_ne_one
  mod_mul := by simp

instance [AddGroup G] : SubSelf G := ⟨by simp⟩

-- instance (priority := 100) AddGroup.toSubSelf [s : AddGroup α] : SubSelf α := ⟨by simp⟩
