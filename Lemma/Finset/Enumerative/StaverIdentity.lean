import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[staver_sign_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
lemma staver_sign_mul
  {n k : ℕ}
-- given
  (hk : k ≤ n) :
-- imply
  (-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ k = (-1 : ℚ) ^ n := by
-- proof
  rw [← pow_add, Nat.sub_add_cancel hk]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[staver_sign_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
lemma staver_sign_sq
  {k : ℕ} :
-- imply
  (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 := by
-- proof
  rw [← pow_add]
  exact Even.neg_one_pow ⟨k, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[staver_sign_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
lemma staver_sign_odd
  {n k : ℕ}
-- given
  (hodd : Odd n)
  (hk : k ≤ n) :
-- imply
  (-1 : ℚ) ^ (n - k) = -(-1 : ℚ) ^ k := by
-- proof
  have hmul := staver_sign_mul n k hk
  have hsq := staver_sign_sq k
  have he1 : (-1 : ℚ) ^ n = -1 := hodd.neg_one_pow
  calc (-1 : ℚ) ^ (n - k) = (-1 : ℚ) ^ (n - k) * 1 := (mul_one _).symm
    _ = (-1 : ℚ) ^ (n - k) * ((-1 : ℚ) ^ k * (-1 : ℚ) ^ k) := by rw [hsq]
    _ = ((-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ k) * (-1 : ℚ) ^ k := by ring
    _ = (-1 : ℚ) ^ n * (-1 : ℚ) ^ k := by rw [hmul]
    _ = -(-1 : ℚ) ^ k := by rw [he1, neg_one_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[staver_sign_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
lemma staver_sign_even
  {n k : ℕ}
-- given
  (heven : Even n)
  (hk : k ≤ n) :
-- imply
  (-1 : ℚ) ^ (n - k) = (-1 : ℚ) ^ k := by
-- proof
  have hmul := staver_sign_mul n k hk
  have hsq := staver_sign_sq k
  have he1 : (-1 : ℚ) ^ n = 1 := heven.neg_one_pow
  calc (-1 : ℚ) ^ (n - k) = (-1 : ℚ) ^ (n - k) * 1 := (mul_one _).symm
    _ = (-1 : ℚ) ^ (n - k) * ((-1 : ℚ) ^ k * (-1 : ℚ) ^ k) := by rw [hsq]
    _ = ((-1 : ℚ) ^ (n - k) * (-1 : ℚ) ^ k) * (-1 : ℚ) ^ k := by ring
    _ = (-1 : ℚ) ^ n * (-1 : ℚ) ^ k := by rw [hmul]
    _ = (-1 : ℚ) ^ k := by rw [he1, one_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[staver_reflect_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
lemma staver_reflect_zero
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) =
    ∑ k ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ k * ((Nat.choose n k : ℚ))⁻¹ := by
-- proof
  rw [← Finset.sum_range_reflect
    (fun k => (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have e1 : n + 1 - 1 - k = n - k := by omega
  have e2 : n - (n - k) = k := by omega
  have e3 : Nat.choose n (n - k) = Nat.choose n k := Nat.choose_symm hkle
  rw [e1, e2, e3]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[staver_reflect_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
lemma staver_reflect_one
  {n : ℕ} :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
    ∑ k ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ k * ((n - k : ℕ) : ℚ) * ((Nat.choose n k : ℚ))⁻¹ := by
-- proof
  rw [← Finset.sum_range_reflect
    (fun k => (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have e1 : n + 1 - 1 - k = n - k := by omega
  have e2 : n - (n - k) = k := by omega
  have e3 : Nat.choose n (n - k) = Nat.choose n k := Nat.choose_symm hkle
  rw [e1, e2, e3]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[staver_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StaverIdentity.lean)
-/
@[path]
lemma staver_identity
  {n : ℕ} :
-- imply
  (Even n →
    ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹ =
    (n : ℚ) / 2 * ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) ∧
    (Odd n →
    ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹ = 0) := by
-- proof
  constructor
  · intro heven
    -- double the weighted sum and pair up
    have h2 : 2 * (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ k * (n : ℚ) * ((Nat.choose n k : ℚ))⁻¹ := by
      have hexpand : 2 * (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
        ∑ k ∈ Finset.range (n + 1),
          (((-1 : ℚ) ^ (n - k) * (k : ℚ) +
            (-1 : ℚ) ^ k * ((n - k : ℕ) : ℚ)) *
            ((Nat.choose n k : ℚ))⁻¹) := by
        rw [two_mul]
        nth_rewrite 2 [staver_reflect_one]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hexpand]
      apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hkn : (k : ℚ) + ((n - k : ℕ) : ℚ) = (n : ℚ) := by
        exact_mod_cast Nat.add_sub_cancel' hkle
      rw [staver_sign_even heven hkle]
      linear_combination ((-1 : ℚ) ^ k * ((Nat.choose n k : ℚ))⁻¹) * hkn
    -- double the scaled unweighted sum to the same target
    have h0 : 2 * ((n : ℚ) / 2 * (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹)) =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ k * (n : ℚ) * ((Nat.choose n k : ℚ))⁻¹ := by
      have hmul : 2 * ((n : ℚ) / 2 * (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹)) =
        2 * ∑ k ∈ Finset.range (n + 1),
          ((n : ℚ) / 2 * ((-1 : ℚ) ^ (n - k) *
            ((Nat.choose n k : ℚ))⁻¹)) := by
        congr 1
        exact Finset.mul_sum _ _ _
      rw [hmul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [staver_sign_even heven hkle]
      ring
    have hdone : 2 * (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * (k : ℚ) * ((Nat.choose n k : ℚ))⁻¹) =
      2 * ((n : ℚ) / 2 * (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹)) := by
      linarith [h2, h0]
    exact mul_left_cancel₀ (by norm_num : (2 : ℚ) ≠ 0) hdone
  · intro hodd
    have h2 : 2 * (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) =
      ∑ k ∈ Finset.range (n + 1),
        (((-1 : ℚ) ^ (n - k) + (-1 : ℚ) ^ k) *
          ((Nat.choose n k : ℚ))⁻¹) := by
      rw [two_mul]
      nth_rewrite 2 [staver_reflect_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hterm : ∀ k ∈ Finset.range (n + 1),
      (((-1 : ℚ) ^ (n - k) + (-1 : ℚ) ^ k) *
        ((Nat.choose n k : ℚ))⁻¹) = 0 := by
      intro k hk
      have hkle : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [staver_sign_odd hodd hkle, neg_add_cancel, zero_mul]
    have hS : 2 * (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * ((Nat.choose n k : ℚ))⁻¹) = 0 := by
      rw [h2]
      exact Finset.sum_eq_zero hterm
    linarith

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
