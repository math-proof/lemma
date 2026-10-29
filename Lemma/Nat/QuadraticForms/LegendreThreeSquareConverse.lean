import Mathlib
import Initialize.Tactic.Attr.Basic


namespace Nat

/--
[sq_mod8](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquareConverse.lean)
-/
@[path]
private lemma sq_mod8 (n : Nat) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  have hpow : n ^ 2 % 8 = (n % 8) ^ 2 % 8 := Nat.pow_mod n 2 8
  have h4 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨
    n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
    have hlt := Nat.mod_lt n (show 0 < 8 from by norm_num)
    omega
  obtain h|h|h|h|h|h|h|h := h4 <;> rw [hpow, h] <;> norm_num

end Nat

namespace Nat

/--
[sq_mod4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquareConverse.lean)
-/
@[path]
private lemma sq_mod4 (n : Nat) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have hpow : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := Nat.pow_mod n 2 4
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    have hlt := Nat.mod_lt n (show 0 < 4 from by norm_num)
    omega
  obtain h|h|h|h := h4 <;> rw [hpow, h] <;> norm_num

end Nat

namespace Nat

/--
[even_of_sq_mod4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquareConverse.lean)
-/
@[path]
private lemma even_of_sq_mod4 {n : Nat} (h : n ^ 2 % 4 = 0) : Even n := by
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    have hlt := Nat.mod_lt n (show 0 < 4 from by norm_num)
    omega
  have hpow : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := Nat.pow_mod n 2 4
  obtain h'|h'|h'|h' := h4
  · clear h hpow
    rw [Nat.even_iff]
    omega
  · rw [hpow, h'] at h; norm_num at h
  · clear h hpow
    rw [Nat.even_iff]
    omega
  · rw [hpow, h'] at h; norm_num at h

end Nat

namespace Nat

/--
[even_of_sum_sq_eq_four_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquareConverse.lean)
-/
@[path]
private lemma even_of_sum_sq_eq_four_mul {x y z m : Nat}
  (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 * m) : Even x ∧ Even y ∧ Even z := by
  have hx := sq_mod4 x
  have hy := sq_mod4 y
  have hz := sq_mod4 z
  have hmod : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0 := by omega
  have hx0 : x ^ 2 % 4 = 0 := by omega
  have hy0 : y ^ 2 % 4 = 0 := by omega
  have hz0 : z ^ 2 % 4 = 0 := by omega
  exact ⟨even_of_sq_mod4 hx0, even_of_sq_mod4 hy0, even_of_sq_mod4 hz0⟩

end Nat

namespace Nat

/--
[key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquareConverse.lean)
-/
@[path]
private lemma key : ∀ (a : Nat) (b x y z : Nat),
  x ^ 2 + y ^ 2 + z ^ 2 = 4 ^ a * (8 * b + 7) → False := by
  intro a
  induction a with
  | zero =>
    intro b x y z h
    have h0 : (4 : Nat) ^ 0 * (8 * b + 7) = 8 * b + 7 := by simp
    have hmod : (x ^ 2 + y ^ 2 + z ^ 2) % 8 = 7 := by omega
    rcases sq_mod8 x with hx | hx | hx <;> rcases sq_mod8 y with hy | hy | hy <;>
      rcases sq_mod8 z with hz | hz | hz <;> omega
  | succ a ih =>
    intro b x y z h
    have h4 : x ^ 2 + y ^ 2 + z ^ 2 = 4 * (4 ^ a * (8 * b + 7)) := by
      have hpow : (4 : Nat) ^ (a + 1) = 4 * 4 ^ a := pow_succ'
      calc x ^ 2 + y ^ 2 + z ^ 2 = 4 ^ (a + 1) * (8 * b + 7) := h
        _ = 4 * (4 ^ a * (8 * b + 7)) := by rw [hpow]; ring
    obtain ⟨hx, hy, hz⟩ :=
      even_of_sum_sq_eq_four_mul (m := 4 ^ a * (8 * b + 7)) h4
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    obtain ⟨z', rfl⟩ := hz
    have hdiv : x' ^ 2 + y' ^ 2 + z' ^ 2 = 4 ^ a * (8 * b + 7) := by
      have h4' : (x' + x') ^ 2 + (y' + y') ^ 2 + (z' + z') ^ 2
        = 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) := by ring
      omega
    exact ih b x' y' z' hdiv

end Nat

namespace Nat

/--
[not_exists_four_pow_mul_eight_mul_add_seven_of_exists_three_squares](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquareConverse.lean)
-/
@[path]
lemma not_exists_four_pow_mul_eight_mul_add_seven_of_exists_three_squares
  {n : Nat}
-- given
  (h : ∃ x y z : Nat, x ^ 2 + y ^ 2 + z ^ 2 = n) :
-- imply
  ¬ ∃ a b : Nat, n = 4 ^ a * (8 * b + 7) := by
-- proof
  obtain ⟨x, y, z, hxyz⟩ := h
  rintro ⟨a, b, hab⟩
  exact key a b x y z (by omega)

end Nat


-- created on 2026-10-20
-- updated on 2026-10-26
