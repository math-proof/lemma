import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[nat_eq_sq_sub_sq_iff_not_eq_four_mul_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/DifferenceOfTwoSquares.lean)
-/
@[path]
lemma nat_eq_sq_sub_sq_iff_not_eq_four_mul_add_two
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∃ a b : ℕ, n = a ^ 2 - b ^ 2) ↔ ¬ ∃ k : ℕ, n = 4 * k + 2 := by
-- proof
  constructor
  · rintro ⟨a, b, hab⟩ ⟨k, hk⟩
    by_cases hle : b ≤ a
    · have h2 : n + b ^ 2 = a ^ 2 := by omega
      have ha4 : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
        have hr : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
        have hp : a ^ 2 % 4 = (a % 4) ^ 2 % 4 := Nat.pow_mod a 2 4
        obtain r | r | r | r := hr <;> rw [hp, r] <;> decide
      have hb4 : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by
        have hr : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
        have hp : b ^ 2 % 4 = (b % 4) ^ 2 % 4 := Nat.pow_mod b 2 4
        obtain r | r | r | r := hr <;> rw [hp, r] <;> decide
      omega
    · have hlt : a < b := lt_of_not_ge hle
      have hzero : a ^ 2 - b ^ 2 = 0 :=
        Nat.sub_eq_zero_of_le (Nat.pow_le_pow_left (le_of_lt hlt) 2)
      omega
  · intro hne
    have hmod2 : n % 4 ≠ 2 := by
      intro hcon
      apply hne
      exact ⟨n / 4, by have h1 := Nat.div_add_mod n 4; omega⟩
    have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 3 := by omega
    clear hne hmod2
    obtain h0 | h1 | h3 := hmod
    · obtain ⟨k, hk⟩ : ∃ k, n = 4 * k := ⟨n / 4, by have hd := Nat.div_add_mod n 4; omega⟩
      have hkpos : 0 < k := by omega
      obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
      refine ⟨t + 2, t, ?_⟩
      have hle : t ^ 2 ≤ (t + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have heq : (t + 2) ^ 2 = 4 * (t + 1) + t ^ 2 := by ring
      omega
    · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 :=
      ⟨2 * (n / 4), by have hd := Nat.div_add_mod n 4; omega⟩
      refine ⟨m + 1, m, ?_⟩
      have hle : m ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have heq : (m + 1) ^ 2 = (2 * m + 1) + m ^ 2 := by ring
      omega
    · obtain ⟨m, hm⟩ : ∃ m, n = 2 * m + 1 :=
      ⟨2 * (n / 4) + 1, by have hd := Nat.div_add_mod n 4; omega⟩
      refine ⟨m + 1, m, ?_⟩
      have hle : m ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have heq : (m + 1) ^ 2 = (2 * m + 1) + m ^ 2 := by ring
      omega

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
