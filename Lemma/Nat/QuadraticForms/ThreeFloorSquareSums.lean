import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[eight_mul_add_three_not_rep](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeFloorSquareSums.lean)
-/
@[path]
private lemma eight_mul_add_three_not_rep (m : ℕ) :
  ¬ ∃ a b : ℕ, 8 * m + 3 = 4 ^ a * (8 * b + 7) := by
  rintro ⟨a, b, h⟩
  cases a with
  | zero =>
    simp only [pow_zero, one_mul] at h
    omega
  | succ k =>
    have h4 : 4 ∣ 4 ^ (k + 1) := dvd_pow_self 4 (Nat.succ_ne_zero k)
    have h2 : 2 ∣ 4 ^ (k + 1) := dvd_trans (by decide) h4
    have hdvd : 2 ∣ 8 * m + 3 := by
      rw [h]
      exact dvd_mul_of_dvd_left h2 _
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sq_mod_eight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeFloorSquareSums.lean)
-/
@[path]
private lemma sq_mod_eight (n : ℕ) :
  n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  have hpow : n ^ 2 % 8 = (n % 8) ^ 2 % 8 := Nat.pow_mod n 2 8
  have hdis : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨
    n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
    have hlt := Nat.mod_lt n (show 0 < 8 from by norm_num)
    omega
  obtain h | h | h | h | h | h | h | h <;> rw [hpow, h] <;> decide := hdis

end MetaMathlibExt

namespace MetaMathlibExt

/--
[even_sq_mod_eight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeFloorSquareSums.lean)
-/
@[path]
private lemma even_sq_mod_eight {x : ℕ} (h : Even x) :
  x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 4 := by
  have hpow : x ^ 2 % 8 = (x % 8) ^ 2 % 8 := Nat.pow_mod x 2 8
  have h2 : x % 2 = 0 := Nat.even_iff.mp h
  have hlt := Nat.mod_lt x (show 0 < 8 from by norm_num)
  have hdis : x % 8 = 0 ∨ x % 8 = 2 ∨ x % 8 = 4 ∨ x % 8 = 6 := by omega
  obtain h0 | h0 | h0 | h0 <;> rw [hpow, h0] <;> decide := hdis

end MetaMathlibExt

namespace MetaMathlibExt

/--
[odd_of_sq_mod_eight_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeFloorSquareSums.lean)
-/
@[path]
private lemma odd_of_sq_mod_eight_eq_one {x : ℕ} (h : x ^ 2 % 8 = 1) :
  Odd x := by
  obtain he | ho := Nat.even_or_odd x
  · have hdis := even_sq_mod_eight he
    omega
  · exact ho

end MetaMathlibExt

namespace MetaMathlibExt

/--
[odd_sq_eight_mul_div_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeFloorSquareSums.lean)
-/
@[path]
private lemma odd_sq_eight_mul_div_add_one {x : ℕ} (h : Odd x) :
  8 * (x ^ 2 / 8) + 1 = x ^ 2 := by
  obtain ⟨t, ht⟩ := h
  have hsq : x ^ 2 = 4 * (t * (t + 1)) + 1 := by
    rw [ht]
    ring
  have heven : Even (t * (t + 1)) := by
    obtain he | ho := Nat.even_or_odd t
    · obtain ⟨k, hk⟩ := he
      exact ⟨k * (t + 1), by rw [hk]; ring⟩
    · obtain ⟨k, hk⟩ := ho
      exact ⟨t * (k + 1), by rw [hk]; ring⟩
  obtain ⟨k, hk⟩ := heven
  have hsq2 : x ^ 2 = 8 * k + 1 := by omega
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[every_nat_eq_sum_three_sq_div_eight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeFloorSquareSums.lean)
-/
@[path]
lemma every_nat_eq_sum_three_sq_div_eight
  {m : ℕ} :
-- imply
  ∃ a b c : ℕ, m = a ^ 2 / 8 + b ^ 2 / 8 + c ^ 2 / 8 := by
-- proof
  have hform : ¬ ∃ a b : ℕ, 8 * m + 3 = 4 ^ a * (8 * b + 7) :=
    eight_mul_add_three_not_rep m
  obtain ⟨x, y, z, hxyz⟩ :=
    Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven
      (8 * m + 3) hform
  have hmod : (x ^ 2 + y ^ 2 + z ^ 2) % 8 = 3 := by omega
  have hx8 := sq_mod_eight x
  have hy8 := sq_mod_eight y
  have hz8 := sq_mod_eight z
  have hx1 : x ^ 2 % 8 = 1 := by omega
  have hy1 : y ^ 2 % 8 = 1 := by omega
  have hz1 : z ^ 2 % 8 = 1 := by omega
  have hox : Odd x := odd_of_sq_mod_eight_eq_one hx1
  have hoy : Odd y := odd_of_sq_mod_eight_eq_one hy1
  have hoz : Odd z := odd_of_sq_mod_eight_eq_one hz1
  have hex := odd_sq_eight_mul_div_add_one hox
  have hey := odd_sq_eight_mul_div_add_one hoy
  have hez := odd_sq_eight_mul_div_add_one hoz
  exact ⟨x, y, z, by omega⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
