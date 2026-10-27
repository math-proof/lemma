import Mathlib
import Initialize.Tactic.Attr.Basic


namespace Nat

/--
[eq_zero_of_three_pow_succ_add_one_eq_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Diophantine/PowerSquare.lean)
-/
@[path]
lemma eq_zero_of_three_pow_succ_add_one_eq_sq
  {y z : ℕ}
-- given
  (h : 3 ^ (y + 1) + 1 = z ^ 2) :
-- imply
  y = 0 := by
-- proof
  have hp : Nat.Prime 3 := by decide
  have h_pow_ge3 : 3 ≤ 3 ^ (y + 1) := by
    calc 3 = 3 ^ 1 := by simp
      _ ≤ 3 ^ (y + 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have h_z_sq_ge4 : 4 ≤ z ^ 2 := by omega
  have hz_ge2 : 2 ≤ z := by
    by_contra hlt
    have hz_le1 : z ≤ 1 := by omega
    have hz_sq_le1 : z ^ 2 ≤ 1 := by nlinarith
    omega
  have hz_ge1 : 1 ≤ z := by omega
  have h_prod : (z - 1) * (z + 1) = 3 ^ (y + 1) := by
    have h1 : z ^ 2 - 1 = 3 ^ (y + 1) := by omega
    have h2 : (z - 1) * (z + 1) = z ^ 2 - 1 := by
      have hz_int : ((z : ℤ) - 1) * ((z : ℤ) + 1) = (z : ℤ) ^ 2 - 1 := by ring
      zify [hz_ge1] at hz_int ⊢
      linarith
    omega
  have hdvd1 : (z - 1) ∣ 3 ^ (y + 1) := ⟨z + 1, h_prod.symm⟩
  have hdvd2 : (z + 1) ∣ 3 ^ (y + 1) := ⟨z - 1, by rw [Nat.mul_comm]; exact h_prod.symm⟩
  obtain ⟨a, _, ha_eq⟩ := (Nat.dvd_prime_pow hp).mp hdvd1
  obtain ⟨b, _, hb_eq⟩ := (Nat.dvd_prime_pow hp).mp hdvd2
  have ha_eq' : z - 1 = 3 ^ a := ha_eq
  have hb_eq' : z + 1 = 3 ^ b := hb_eq
  have h_lt : z - 1 < z + 1 := by omega
  have h_pow_lt : 3 ^ a < 3 ^ b := by
    calc 3 ^ a = z - 1 := ha_eq'.symm
      _ < z + 1 := h_lt
      _ = 3 ^ b := hb_eq'
  have hab_lt : a < b := (Nat.pow_lt_pow_iff_right (by decide)).mp h_pow_lt
  have h_le_pow : 3 ^ a ≤ 3 ^ b := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hab_lt)
  have h_diff : 3 ^ b - 3 ^ a = 2 := by
    have h_eq_sub : z + 1 - (z - 1) = 3 ^ b - 3 ^ a := by
      rw [hb_eq', ha_eq']
    have h_sub_val : z + 1 - (z - 1) = 2 := by omega
    omega
  have h_not_dvd : ¬3 ∣ 2 := by decide
  have ha0 : a = 0 := by
    by_contra ha_ne
    have hb_ne : b ≠ 0 := by omega
    have h_dvd_a : 3 ∣ 3 ^ a := dvd_pow_self 3 ha_ne
    have h_dvd_b : 3 ∣ 3 ^ b := dvd_pow_self 3 hb_ne
    have h_dvd_diff : 3 ∣ 3 ^ b - 3 ^ a :=
      Nat.dvd_sub h_dvd_b h_dvd_a
    have h_dvd_2 : 3 ∣ 2 := h_diff ▸ h_dvd_diff
    exact h_not_dvd h_dvd_2
  have ha_pow1 : 3 ^ a = 1 := by simp [ha0]
  have hb_pow3 : 3 ^ b = 3 := by omega
  have hz1_eq1 : z - 1 = 1 := by
    calc z - 1 = 3 ^ a := ha_eq'
      _ = 1 := ha_pow1
  have hz2_eq3 : z + 1 = 3 := by
    calc z + 1 = 3 ^ b := hb_eq'
      _ = 3 := hb_pow3
  have h_pow_eq3 : 3 ^ (y + 1) = 3 := by
    calc 3 ^ (y + 1) = (z - 1) * (z + 1) := h_prod.symm
      _ = 1 * 3 := by rw [hz1_eq1, hz2_eq3]
      _ = 3 := by decide
  have hy1 : y + 1 = 1 := by
    by_contra hy_ne
    have hy_ge2 : 2 ≤ y + 1 := by omega
    have h9_le : 9 ≤ 3 ^ (y + 1) := by
      calc 9 = 3 ^ 2 := by decide
        _ ≤ 3 ^ (y + 1) := Nat.pow_le_pow_right (by decide) hy_ge2
    omega
  omega

end Nat


-- created on 2026-10-20
-- updated on 2026-10-26
