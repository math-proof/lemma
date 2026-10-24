import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

def dedekindSaw (x : ℚ) : ℚ :=
  if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

theorem dedekindSaw_of_fract_eq_zero {x : ℚ} (h : Int.fract x = 0) : dedekindSaw x = 0 :=
  if_pos h

theorem dedekindSaw_of_fract_ne_zero {x : ℚ} (h : Int.fract x ≠ 0) :
    dedekindSaw x = Int.fract x - 1 / 2 :=
  if_neg h

theorem dedekindSaw_intCast (n : ℤ) : dedekindSaw (n : ℚ) = 0 :=
  dedekindSaw_of_fract_eq_zero (Int.fract_intCast n)

theorem dedekindSaw_natCast (n : ℕ) : dedekindSaw (n : ℚ) = 0 := by
  rw [← Int.cast_natCast]; exact dedekindSaw_intCast (n : ℤ)

theorem dedekindSaw_zero : dedekindSaw 0 = 0 := by
  rw [← Int.cast_zero]; exact dedekindSaw_intCast 0

theorem dedekindSaw_one : dedekindSaw 1 = 0 := by
  rw [← Int.cast_one]; exact dedekindSaw_intCast 1

theorem dedekindSaw_add_intCast (x : ℚ) (n : ℤ) : dedekindSaw (x + n) = dedekindSaw x := by
  unfold dedekindSaw
  rw [Int.fract_add_intCast]

theorem dedekindSaw_intCast_add (n : ℤ) (x : ℚ) : dedekindSaw ((n : ℚ) + x) = dedekindSaw x := by
  rw [add_comm, dedekindSaw_add_intCast]

theorem dedekindSaw_add_natCast (x : ℚ) (n : ℕ) : dedekindSaw (x + n) = dedekindSaw x := by
  rw [← Int.cast_natCast]; exact dedekindSaw_add_intCast x (n : ℤ)

theorem dedekindSaw_neg (x : ℚ) : dedekindSaw (-x) = -dedekindSaw x := by
  unfold dedekindSaw
  by_cases h : Int.fract x = 0
  · rw [if_pos h, if_pos (Int.fract_neg_eq_zero.2 h), neg_zero]
  · rw [if_neg h, if_neg fun h' => h (Int.fract_neg_eq_zero.1 h'), Int.fract_neg h]
    ring

theorem abs_dedekindSaw_lt_half (x : ℚ) : |dedekindSaw x| < 1 / 2 := by
  unfold dedekindSaw
  by_cases h : Int.fract x = 0
  · rw [if_pos h, abs_zero]
    exact one_half_pos
  · have h0 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm h)
    have h1 : Int.fract x < 1 := Int.fract_lt_one x
    rw [if_neg h, abs_lt]
    constructor <;> linarith

theorem dedekindSaw_half : dedekindSaw (1 / 2) = 0 := by
  have hfr : Int.fract (1 / 2 : ℚ) = 1 / 2 :=
    Int.fract_eq_self.2 ⟨one_half_pos.le, one_half_lt_one⟩
  rw [dedekindSaw_of_fract_ne_zero (by rw [hfr]; exact one_half_pos.ne'), hfr, sub_self]

theorem dedekindSaw_natCast_div {r k : ℕ} (h0 : 0 < r) (hrk : r < k) :
    dedekindSaw ((r : ℚ) / k) = (r : ℚ) / k - 1 / 2 := by
  have hk : (0 : ℚ) < k := by exact_mod_cast h0.trans hrk
  have hpos : (0 : ℚ) < (r : ℚ) / k := div_pos (by exact_mod_cast h0) hk
  have hlt : (r : ℚ) / k < 1 := (div_lt_one hk).2 (by exact_mod_cast hrk)
  have hfr : Int.fract ((r : ℚ) / k) = (r : ℚ) / k := Int.fract_eq_self.2 ⟨hpos.le, hlt⟩
  rw [dedekindSaw_of_fract_ne_zero (by rw [hfr]; exact hpos.ne'), hfr]

def dedekindSum (h : ℤ) (k : ℕ) : ℚ :=
  ∑ r ∈ Finset.range k, dedekindSaw ((r : ℚ) / k) * dedekindSaw ((h : ℚ) * r / k)

theorem dedekindSum_zero_right (h : ℤ) : dedekindSum h 0 = 0 := by
  simp [dedekindSum]

theorem dedekindSum_one_right (h : ℤ) : dedekindSum h 1 = 0 := by
  simp [dedekindSum, dedekindSaw_zero]

theorem dedekindSum_zero_left (k : ℕ) : dedekindSum 0 k = 0 := by
  simp [dedekindSum, dedekindSaw_zero]

theorem dedekindSum_neg (h : ℤ) (k : ℕ) : dedekindSum (-h) k = -dedekindSum h k := by
  unfold dedekindSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Int.cast_neg, neg_mul, neg_div, dedekindSaw_neg]
  ring

theorem dedekindSum_add_mul (h m : ℤ) (k : ℕ) : dedekindSum (h + m * k) k = dedekindSum h k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [dedekindSum_zero_right, dedekindSum_zero_right]
  unfold dedekindSum
  refine Finset.sum_congr rfl fun r _ => ?_
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have key : ((h + m * k : ℤ) : ℚ) * r / k = (h : ℚ) * r / k + ((m * r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [key, dedekindSaw_add_intCast]

theorem dedekindSum_eq_sum_Ico (h : ℤ) (k : ℕ) :
    dedekindSum h k =
      ∑ r ∈ Finset.Ico 1 k, ((r : ℚ) / k - 1 / 2) * dedekindSaw ((h : ℚ) * r / k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [dedekindSum_zero_right]
    simp
  unfold dedekindSum
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk, zero_add]
  simp only [Nat.cast_zero, zero_div, dedekindSaw_zero, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hr
  rw [dedekindSaw_natCast_div h1 h2]
