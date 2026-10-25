import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.BAryBinomialCoefficient
import Lemma.Finset.Enumerative.BAryBinomialCoefficient


namespace MetaMathlibExt

/--
[bary_mod_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
private lemma bary_mod_mul (b L x : ℕ) (hb : 2 ≤ b) :
  x % (b * b ^ L) = x % b + b * ((x / b) % b ^ L) := by
  have hb0 : 0 < b := by omega
  have hM : 0 < b ^ L := pow_pos hb0 L
  have hr0 : x % b < b := Nat.mod_lt x hb0
  have hq : (x / b) % b ^ L < b ^ L := Nat.mod_lt _ hM
  have hY : (x / b) % b ^ L + 1 ≤ b ^ L := Nat.succ_le_of_lt hq
  have hA : x % b + b * ((x / b) % b ^ L) < b * b ^ L := by
    calc x % b + b * ((x / b) % b ^ L)
      < b + b * ((x / b) % b ^ L) := Nat.add_lt_add_right hr0 _
      _ = b * (((x / b) % b ^ L) + 1) := by ring
      _ ≤ b * b ^ L := Nat.mul_le_mul_left b hY
  have h2 := Nat.div_add_mod (x / b) (b ^ L)
  have hQR : b * (x / b) = (b * b ^ L) * ((x / b) / b ^ L) + b * ((x / b) % b ^ L) := by
    conv_lhs => rw [← h2]
    ring
  have h1 := Nat.div_add_mod x b
  have hx : x = (x % b + b * ((x / b) % b ^ L)) + (b * b ^ L) * ((x / b) / b ^ L) := by
    calc x = b * (x / b) + x % b := h1.symm
      _ = (x % b + b * ((x / b) % b ^ L)) + (b * b ^ L) * ((x / b) / b ^ L) := by
        rw [hQR]; ring
  conv_lhs => rw [hx]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bary_sum_digits_mod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
private lemma bary_sum_digits_mod (b x L : ℕ) (hb : 2 ≤ b) :
  ∑ l ∈ Finset.range L, ((x / b ^ l) % b) * b ^ l = x % b ^ L := by
  induction L generalizing x with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, pow_zero, Nat.mod_one]
  | succ L ih =>
    have hshift : ∀ l ∈ Finset.range L, ((x / b ^ (l + 1)) % b) * b ^ (l + 1)
      = b * ((((x / b) / b ^ l) % b) * b ^ l) := by
      intro l _
      have hdiv : x / b ^ (l + 1) = (x / b) / b ^ l := by
        rw [pow_succ', Nat.div_div_eq_div_mul]
      rw [hdiv, pow_succ']
      ring
    have hS : (∑ l ∈ Finset.range L, ((x / b ^ (l + 1)) % b) * b ^ (l + 1))
      = b * ((x / b) % b ^ L) := by
      rw [Finset.sum_congr rfl hshift, ← Finset.mul_sum, ih (x / b)]
    rw [Finset.sum_range_succ', hS]
    simp only [pow_zero, Nat.div_one, mul_one]
    rw [pow_succ', add_comm (b * ((x / b) % b ^ L)) (x % b)]
    exact (bary_mod_mul b L x hb).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bary_mod_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
private lemma bary_mod_sum_le (b l m n : ℕ) (hb : 2 ≤ b)
  (hfree : ∀ j ∈ Finset.range l, (m / b ^ j) % b + (n / b ^ j) % b < b) :
  m % b ^ l + n % b ^ l + 1 ≤ b ^ l := by
  induction l generalizing m n with
  | zero =>
    have e1 : m % (1 : ℕ) = 0 := Nat.mod_one m
    have e2 : n % (1 : ℕ) = 0 := Nat.mod_one n
    rw [pow_zero]
    omega
  | succ l ih =>
    have hside : ∀ j ∈ Finset.range l, ((m / b) / b ^ j) % b + ((n / b) / b ^ j) % b < b := by
      intro j hj
      have hmem : j + 1 ∈ Finset.range (l + 1) := by
        simp only [Finset.mem_range] at hj ⊢; omega
      have hfree' := hfree (j + 1) hmem
      have e1 : (m / b) / b ^ j = m / b ^ (j + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ']
      have e2 : (n / b) / b ^ j = n / b ^ (j + 1) := by
        rw [Nat.div_div_eq_div_mul, pow_succ']
      rwa [e1, e2]
    have hB : (m / b) % b ^ l + (n / b) % b ^ l + 1 ≤ b ^ l := ih _ _ hside
    have h0 : (m / b ^ 0) % b + (n / b ^ 0) % b < b := hfree 0 (by simp)
    simp only [pow_zero, Nat.div_one] at h0
    have hA : m % b + n % b + 1 ≤ b := Nat.succ_le_of_lt h0
    have hmul : b * (((m / b) % b ^ l + (n / b) % b ^ l) + 1) ≤ b * b ^ l :=
      Nat.mul_le_mul_left b hB
    rw [pow_succ', bary_mod_mul b l m hb, bary_mod_mul b l n hb]
    calc m % b + b * ((m / b) % b ^ l) + (n % b + b * ((n / b) % b ^ l)) + 1
      = (m % b + n % b + 1) + b * (((m / b) % b ^ l) + ((n / b) % b ^ l)) := by ring
      _ ≤ b + b * (((m / b) % b ^ l) + ((n / b) % b ^ l)) :=
        Nat.add_le_add_right hA _
      _ = b * ((((m / b) % b ^ l) + ((n / b) % b ^ l)) + 1) := by ring
      _ ≤ b * b ^ l := hmul

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bary_div_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
private lemma bary_div_add (b l m n : ℕ) (hb : 2 ≤ b)
  (hfree : ∀ j ∈ Finset.range l, (m / b ^ j) % b + (n / b ^ j) % b < b) :
  (m + n) / b ^ l = m / b ^ l + n / b ^ l := by
  have hR : m % b ^ l + n % b ^ l < b ^ l := by
    have hle := bary_mod_sum_le b l m n hb hfree
    omega
  have hM : 0 < b ^ l := pow_pos (by omega) l
  have hdm := Nat.div_add_mod m (b ^ l)
  have hdn := Nat.div_add_mod n (b ^ l)
  have hdecomp : m + n = (m % b ^ l + n % b ^ l) + b ^ l * (m / b ^ l + n / b ^ l) := by
    conv_lhs => rw [← hdm, ← hdn]
    ring
  rw [hdecomp, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hR, Nat.zero_add]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bary_digit_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
private lemma bary_digit_add (b l m n : ℕ) (hb : 2 ≤ b)
  (hfree : ∀ j ∈ Finset.range l, (m / b ^ j) % b + (n / b ^ j) % b < b)
  (hl : (m / b ^ l) % b + (n / b ^ l) % b < b) :
  ((m + n) / b ^ l) % b = (m / b ^ l) % b + (n / b ^ l) % b := by
  rw [bary_div_add b l m n hb hfree, Nat.add_mod, Nat.mod_eq_of_lt hl]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bary_lt_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
private lemma bary_lt_pow (b x L : ℕ) (hb : 2 ≤ b) (h : x < L) : x < b ^ L :=
  calc x < L := h
    _ < 2 ^ L := Nat.lt_two_pow_self
    _ ≤ b ^ L := Nat.pow_le_pow_left hb L

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bary_carry_free](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
position. -/
private lemma bary_carry_free (b m n : ℕ) (hb : 2 ≤ b)
  (hcarry : ∀ l ∈ Finset.range (m + n + 1), (m / b ^ l) % b + (n / b ^ l) % b < b) (l : ℕ) :
  (m / b ^ l) % b + (n / b ^ l) % b < b := by
  by_cases hl : l < m + n + 1
  · exact hcarry l (Finset.mem_range.mpr hl)
  · have hmn := bary_lt_pow b (m + n) l hb (by omega)
    rw [Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.le_add_right m n) hmn),
      Nat.div_eq_of_lt (lt_of_le_of_lt (Nat.le_add_left n m) hmn), Nat.zero_mod]
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bary_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
private lemma bary_eq_zero_of_lt (b n k : ℕ) (hb : 2 ≤ b) (h : n < k) :
  bAryBinomialCoefficient b n k hb = 0 := by
  have hn := bary_lt_pow b n (n + k + 1) hb (by omega)
  have hk := bary_lt_pow b k (n + k + 1) hb (by omega)
  rw [bAryBinomialCoefficient_eq_prod_div_pow b n k hb hn hk]
  by_contra h0
  have hle : ∀ l ∈ Finset.range (n + k + 1), (k / b ^ l) % b ≤ (n / b ^ l) % b :=
    fun l hl => not_lt.mp fun hlt => h0 (Finset.prod_eq_zero hl (Nat.choose_eq_zero_of_lt hlt))
  have hsum := Finset.sum_le_sum fun l hl => Nat.mul_le_mul_right (b ^ l) (hle l hl)
  rw [bary_sum_digits_mod b k _ hb, bary_sum_digits_mod b n _ hb, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt hn] at hsum
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bary_gf_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
positions covering the base-`b` digits of `n`. -/
private lemma bary_gf_range (b n L : ℕ) (hb : 2 ≤ b) (hn : n < b ^ L) :
  ∑ k ∈ Finset.range (n + 1),
    (bAryBinomialCoefficient b n k hb : Polynomial ℕ) * Polynomial.X ^ k
    = ∏ l ∈ Finset.range L, (1 + Polynomial.X ^ b ^ l) ^ ((n / b ^ l) % b) := by
  rw [bAryBinomialCoefficient_generating_function]
  simp only [Nat.getD_digits _ _ hb]
  refine Finset.prod_subset (Finset.range_subset_range.mpr
    ((Nat.digits_length_le_iff (by omega) n).mpr hn)) fun l _ hl => ?_
  rw [Finset.mem_range, not_lt, Nat.digits_length_le_iff (b := b) (by omega)] at hl
  rw [Nat.div_eq_of_lt hl, Nat.zero_mod, pow_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bary_gf_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
private lemma bary_gf_coeff (b n r : ℕ) (hb : 2 ≤ b) :
  (∑ k ∈ Finset.range (n + 1),
    (bAryBinomialCoefficient b n k hb : Polynomial ℕ) * Polynomial.X ^ k).coeff r
    = bAryBinomialCoefficient b n r hb := by
  simp only [Polynomial.finsetSum_coeff, ← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul_X_pow,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with hr
  · rfl
  · exact (bary_eq_zero_of_lt b n r hb (by omega)).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bAryBinomialCoefficient_chu_vandermonde](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
lemma bAryBinomialCoefficient_chu_vandermonde
  {b m n r : ℕ}
-- given
  (hb : 2 ≤ b)
  (hcarry : ∀ l, (m / b ^ l) % b + (n / b ^ l) % b < b) :
-- imply
  bAryBinomialCoefficient b (m + n) r hb =
    ∑ k ∈ Finset.range (r + 1),
    bAryBinomialCoefficient b m k hb * bAryBinomialCoefficient b n (r - k) hb := by
-- proof
  have hL := bary_lt_pow b (m + n) (m + n + 1) hb (by omega)
  have hP : (∑ k ∈ Finset.range (m + n + 1),
    (bAryBinomialCoefficient b (m + n) k hb : Polynomial ℕ) * Polynomial.X ^ k)
    = (∑ k ∈ Finset.range (m + 1),
      (bAryBinomialCoefficient b m k hb : Polynomial ℕ) * Polynomial.X ^ k)
      * ∑ k ∈ Finset.range (n + 1),
        (bAryBinomialCoefficient b n k hb : Polynomial ℕ) * Polynomial.X ^ k := by
    rw [bary_gf_range b (m + n) (m + n + 1) hb hL,
      bary_gf_range b m (m + n + 1) hb (lt_of_le_of_lt (Nat.le_add_right m n) hL),
      bary_gf_range b n (m + n + 1) hb (lt_of_le_of_lt (Nat.le_add_left n m) hL),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [bary_digit_add b l m n hb (fun j _ => hcarry j) (hcarry l), pow_add]
  have hc := congrArg (Polynomial.coeff · r) hP
  simp only [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    bary_gf_coeff] at hc
  exact hc

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bary_chu_vandermonde](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryChuVandermonde.lean)
-/
@[path]
lemma bary_chu_vandermonde
  {b m n r : ℕ}
-- given
  (hb : 2 ≤ b)
  (hcarry : ∀ l ∈ Finset.range (m + n + 1), (m / b ^ l) % b + (n / b ^ l) % b < b) :
-- imply
  (let C : ℕ → ℕ → ℕ := by
-- proof
  intro C
  have hC : ∀ x y, C x y = bAryBinomialCoefficient b x y hb := fun x y =>
    (bAryBinomialCoefficient_eq_prod_div_pow b x y hb (L := x + y + 1)
      (bary_lt_pow b x _ hb (by omega)) (bary_lt_pow b y _ hb (by omega))).symm
  simp only [hC]
  exact bAryBinomialCoefficient_chu_vandermonde b m n r hb (bary_carry_free b m n hb hcarry)

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
