import Mathlib

set_option autoImplicit false

namespace HopfAlgebra.KummerRadicands

variable {O : Type*} [CommRing O] {n : ℕ} {t : ℕ} (u : Fin t → Oˣ)

def rad (k : Fin t → ZMod n) : Oˣ := ∏ i, u i ^ (k i).val

def carry (k k' : Fin t → ZMod n) : Oˣ := ∏ i, (u i)⁻¹ ^ (((k i).val + (k' i).val) / n)

theorem rad_zero : rad u (0 : Fin t → ZMod n) = 1 := by
  simp [rad]

theorem carry_comm (k k' : Fin t → ZMod n) : carry u k k' = carry u k' k := by
  simp only [carry, Nat.add_comm (k _).val]

variable [NeZero n]

theorem carry_zero_left (k : Fin t → ZMod n) : carry u 0 k = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Pi.zero_apply, ZMod.val_zero, zero_add, Nat.div_eq_of_lt (ZMod.val_lt (k i)), pow_zero]

theorem carry_zero_right (k : Fin t → ZMod n) : carry u k 0 = 1 := by
  rw [carry_comm, carry_zero_left]

theorem inv_pow_div_pow_mul (v : Oˣ) (a b : ZMod n) :
    (v⁻¹ ^ ((a.val + b.val) / n)) ^ n * (v ^ a.val * v ^ b.val) = v ^ (a + b).val := by
  rw [← pow_add, ZMod.val_add]
  set s := a.val + b.val
  have h := Nat.mod_add_div s n
  calc (v⁻¹ ^ (s / n)) ^ n * v ^ s = (v⁻¹ ^ (s / n)) ^ n * v ^ (s % n + n * (s / n)) := by rw [h]
    _ = v ^ (s % n) * ((v⁻¹ ^ (s / n)) ^ n * (v ^ (s / n)) ^ n) := by
        rw [pow_add, pow_mul', mul_left_comm]
    _ = v ^ (s % n) := by rw [← mul_pow, inv_pow, inv_mul_cancel, one_pow, mul_one]

theorem carry_pow_mul_rad_mul_rad (k k' : Fin t → ZMod n) :
    carry u k k' ^ n * (rad u k * rad u k') = rad u (k + k') := by
  simp only [carry, rad, ← Finset.prod_pow, ← Finset.prod_mul_distrib, Pi.add_apply]
  exact Finset.prod_congr rfl fun i _ => inv_pow_div_pow_mul (u i) (k i) (k' i)

omit [NeZero n] in

theorem div_add_mod_add_div (a b c : ℕ) (hn : 0 < n) :
    (a + b) / n + ((a + b) % n + c) / n = (b + c) / n + (a + (b + c) % n) / n := by
  have h1 : (a + b + c) / n = (a + b) / n + ((a + b) % n + c) / n := by
    conv_lhs => rw [← Nat.mod_add_div (a + b) n, add_right_comm, Nat.add_mul_div_left _ _ hn]
    omega
  have h2 : (a + b + c) / n = (b + c) / n + (a + (b + c) % n) / n := by
    conv_lhs => rw [add_assoc, ← Nat.mod_add_div (b + c) n, ← add_assoc, Nat.add_mul_div_left _ _ hn]
    omega
  omega

theorem carry_mul_carry_add (k k' k'' : Fin t → ZMod n) :
    carry u k k' * carry u (k + k') k'' = carry u k' k'' * carry u k (k' + k'') := by
  simp only [carry, ← Finset.prod_mul_distrib, Pi.add_apply]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add, ← pow_add, ZMod.val_add, ZMod.val_add, div_add_mod_add_div _ _ _ (NeZero.pos n)]

end HopfAlgebra.KummerRadicands
