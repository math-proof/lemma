import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.CohnTwiceSquareLucas
open MetaMathlibExt


namespace MetaMathlibExt

/--
[lz_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma lz_zero : lz 0 = 2 :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lz_six](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma lz_six : lz 6 = 18 := by
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lz_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma lz_add_two (n : ℕ) : lz (n + 2) = lz (n + 1) + lz n := by
simp [lz, lucasNumber]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lucN_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma lucN_add_two (n : ℕ) : lucasNumber (n + 2) = lucasNumber (n + 1) + lucasNumber
  n := by
simp [lucasNumber]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cassini](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma cassini (b : ℕ) : lz (b + 1) ^ 2 - lz (b + 1) * lz b - lz b ^ 2 = 5 * (-1) ^
  (b + 1) := by
  induction b with
  | zero => decide
  | succ b ih =>
    have hrec : lz (b + 2) = lz (b + 1) + lz b := lz_add_two b
    have h1 : (b + 1 + 1) = (b + 2) := by omega
    rw [h1, hrec]
    have h2 : (-1 : ℤ) ^ (b + 1 + 1) = -(-1) ^ (b + 1) := by ring
    rw [h2]
    linear_combination -ih

end MetaMathlibExt

namespace MetaMathlibExt

/--
[double_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma double_pair (b : ℕ) : lz (2 * b) = lz b ^ 2 - 2 * (-1) ^ b ∧ lz (2 * b + 1) = lz
  (b + 1) * lz b - (-1) ^ b := by
  induction b with
  | zero => constructor <;> decide
  | succ b ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have hsign : (-1 : ℤ) ^ (b + 1) = -(-1) ^ b := by ring
    have hc := cassini b
    rw [hsign] at hc
    have e1 : 2 * (b + 1) = 2 * b + 2 := by omega
    have e2 : 2 * (b + 1) + 1 = (2 * b + 1) + 2 := by omega
    have e3 : b + 1 + 1 = b + 2 := by omega
    have e5 : 2 * b + 1 + 1 = 2 * (b + 1) := by omega
    have g1 : lz (2 * (b + 1)) = lz (b + 1) ^ 2 - 2 * (-1) ^ (b + 1) := by
      rw [e1, lz_add_two (2 * b), ih0, ih1, hsign]
      linear_combination -hc
    constructor
    · exact g1
    · rw [e2, lz_add_two (2 * b + 1), e5, g1, ih1, e3, lz_add_two b]
      linear_combination -hsign

end MetaMathlibExt

namespace MetaMathlibExt

/--
[lz_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma lz_one : lz 1 = 1 :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[add_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma add_identity (b a : ℕ) : lz (a + 2 * b) = lz (a + b) * lz b - (-1) ^ b * lz a := by
  induction a using Nat.twoStepInduction with
  | zero =>
    have z1 : 0 + 2 * b = 2 * b := by omega
    have z2 : 0 + b = b := by omega
    rw [z1, z2, (double_pair b).1, lz_zero]
    ring
  | one =>
    have o1 : 1 + 2 * b = 2 * b + 1 := by omega
    have o2 : 1 + b = b + 1 := by omega
    rw [o1, o2, (double_pair b).2, lz_one, mul_one]
  | more a iha iha1 =>
    have f1 : (a + 2) + 2 * b = (a + 2 * b) + 2 := by omega
    have f2 : (a + 2 * b) + 1 = (a + 1) + 2 * b := by omega
    have f3 : (a + 2) + b = (a + b) + 2 := by omega
    have f4 : (a + 1) + b = (a + b) + 1 := by omega
    rw [f1, lz_add_two (a + 2 * b), f2, iha1, iha, f3, lz_add_two (a + b), f4, lz_add_two a]
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[iterate_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma iterate_dvd (k : ℕ) (hk : Even k) (a j : ℕ) : lz k ∣ lz (a + 2 * k * j) - (-1 : ℤ) ^
  j * lz a := by
  induction j with
  | zero =>
    have z1 : a + 2 * k * 0 = a := by omega
    rw [z1]
    simp
  | succ j ih =>
    have hk1 : (-1 : ℤ) ^ k = 1 := hk.neg_one_pow
    have hj1 : (-1 : ℤ) ^ (j + 1) = -(-1) ^ j := by ring
    have f1 : a + 2 * k * (j + 1) = (a + 2 * k * j) + 2 * k := by ring
    have hadd := add_identity k (a + 2 * k * j)
    rw [f1, hadd, hk1, hj1]
    have hdecomp : lz ((a + 2 * k * j) + k) * lz k - 1 * lz (a + 2 * k * j) - -(-1 : ℤ) ^ j * lz a =
      lz k * lz ((a + 2 * k * j) + k) - (lz (a + 2 * k * j) - (-1) ^ j * lz a) := by ring
    rw [hdecomp]
    exact dvd_sub (dvd_mul_right _ _) ih

end MetaMathlibExt

namespace MetaMathlibExt

/--
[hdbN](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma hdbN (m : ℕ) (hm : Even m) : lucasNumber (2 * m) + 2 = lucasNumber m ^ 2 := by
  have h := (double_pair m).1
  rw [hm.neg_one_pow] at h
  have h2 : ((lucasNumber (2 * m) : ℕ) : ℤ) + 2 = ((lucasNumber m : ℕ) : ℤ) ^ 2 := by
    change lz (2 * m) + 2 = lz m ^ 2
    linear_combination h
  exact_mod_cast h2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[even_two_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma even_two_pow (g : ℕ) (hg : 1 ≤ g) : Even (2 ^ g) := by
  obtain ⟨g', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : g ≠ 0)
  exact ⟨2 ^ g', by rw [pow_succ']; ring⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[valuation_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma valuation_ge (m e j t : ℕ) (hj : Odd j) (hm : m = 2 ^ e * j) (hd : 2 ^ t ∣ m) : t ≤
  e := by
  by_contra hlt
  have hlt' : e < t := not_le.mp hlt
  obtain ⟨d, rfl⟩ : ∃ d, t = e + (d + 1) := ⟨t - e - 1, by omega⟩
  rw [pow_add] at hd
  rw [hm] at hd
  have h2 : 2 ^ (d + 1) ∣ j := Nat.dvd_of_mul_dvd_mul_left (by positivity) hd
  have h2j : 2 ∣ j := dvd_trans (dvd_pow_self 2 (by omega : d + 1 ≠ 0)) h2
  obtain ⟨k, hk⟩ := hj
  obtain ⟨s, hs⟩ := h2j
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pow2_odd_mod4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma pow2_odd_mod4 (g : ℕ) (hg : 1 ≤ g) : Odd (lucasNumber (2 ^ g)) ∧ lucasNumber (2 ^ g)
  % 4 = 3 := by
  induction g, hg using Nat.le_induction with
  | base => exact ⟨by decide, by decide⟩
  | succ n hn ih =>
    obtain ⟨ihodd, ihmod⟩ := ih
    have hev : Even (2 ^ n) := even_two_pow n hn
    have e : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have hdb := hdbN (2 ^ n) hev
    rw [← e] at hdb
    have hY : Odd ((lucasNumber (2 ^ n)) ^ 2) := ihodd.pow
    obtain ⟨t, ht⟩ := hY
    have hodd : Odd (lucasNumber (2 ^ (n + 1))) := ⟨t - 1, by omega⟩
    have hsq : (lucasNumber (2 ^ n)) ^ 2 % 4 = 1 := by
      have hpm := Nat.pow_mod (lucasNumber (2 ^ n)) 2 4
      rw [ihmod] at hpm
      norm_num at hpm
      exact hpm
    have hmod : lucasNumber (2 ^ (n + 1)) % 4 = 3 := by omega
    exact ⟨hodd, hmod⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pow2_not3dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma pow2_not3dvd (g : ℕ) (hg : 2 ≤ g) : ¬ 3 ∣ lucasNumber (2 ^ g) := by
  obtain ⟨g', rfl⟩ := Nat.exists_eq_add_of_le hg
  have hev : Even (2 ^ (1 + g')) := even_two_pow (1 + g') (by omega)
  have e : 2 ^ (2 + g') = 2 * 2 ^ (1 + g') := by ring
  have hdb := hdbN (2 ^ (1 + g')) hev
  rw [← e] at hdb
  intro hdvd
  obtain ⟨t, ht⟩ := hdvd
  have hsq : (lucasNumber (2 ^ (1 + g'))) ^ 2 % 3 = 0 ∨ (lucasNumber (2 ^ (1 + g'))) ^ 2 % 3 =
    1 := by
    have e3 := Nat.pow_mod (lucasNumber (2 ^ (1 + g'))) 2 3
    have hc : lucasNumber (2 ^ (1 + g')) % 3 = 0 ∨ lucasNumber (2 ^ (1 + g')) % 3 = 1 ∨ lucasNumber
      (2 ^ (1 + g')) % 3 = 2 := by
      have hlt := Nat.mod_lt (lucasNumber (2 ^ (1 + g'))) (by norm_num : 0 < 3)
      omega
    obtain h | h | h <;> rw [e3, h] <;> decide := hc
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mod8_period](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma mod8_period (m : ℕ) : lucasNumber (m + 12) % 8 = lucasNumber m % 8 := by
  induction m using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more m ih0 ih1 =>
    have f1 : m + 2 + 12 = (m + 12) + 2 := by omega
    have f2 : (m + 1) + 12 = (m + 12) + 1 := by omega
    rw [f2] at ih1
    have h1 : lucasNumber (m + 2 + 12) = lucasNumber ((m + 12) + 1) + lucasNumber (m + 12) := by
      rw [f1, lucN_add_two]
    have h2 : lucasNumber (m + 2) = lucasNumber (m + 1) + lucasNumber m := lucN_add_two m
    rw [h1, h2, Nat.add_mod, ih1, ih0, ← Nat.add_mod]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mod8_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma mod8_add (k r : ℕ) : lucasNumber (12 * k + r) % 8 = lucasNumber r % 8 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have f : 12 * (k + 1) + r = (12 * k + r) + 12 := by omega
    rwa [f, mod8_period]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[mod12_cases](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma mod12_cases (n x : ℕ) (h : lucasNumber n = 2 * x ^ 2) : n % 12 = 0 ∨ n % 12 =
  6 := by
  have hper : lucasNumber n % 8 = lucasNumber (n % 12) % 8 := by
    have h1 := mod8_add (n / 12) (n % 12)
    rwa [Nat.div_add_mod] at h1
  have hL : lucasNumber n % 8 = (2 * x ^ 2) % 8 := by rw [h]
  have e2 : (2 * x ^ 2) % 8 = ((2 % 8) * (x ^ 2 % 8)) % 8 := Nat.mul_mod 2 (x ^ 2) 8
  have e1 : x ^ 2 % 8 = ((x % 8) ^ 2) % 8 := Nat.pow_mod x 2 8
  have hx : x % 8 < 8 := Nat.mod_lt (x) (by norm_num)
  have hcases : x % 8 = 0 ∨ x % 8 = 1 ∨ x % 8 = 2 ∨ x % 8 = 3 ∨ x % 8 = 4 ∨ x % 8 = 5 ∨ x % 8 = 6 ∨
    x % 8 = 7 := by omega
  have hsq : x ^ 2 % 8 = 0 ∨ x ^ 2 % 8 = 1 ∨ x ^ 2 % 8 = 4 := by
    obtain h | h | h | h | h | h | h | h <;> rw [e1, h] <;> decide := hcases
  have h28 : (2 * x ^ 2) % 8 = 0 ∨ (2 * x ^ 2) % 8 = 2 := by
    obtain h | h | h <;> rw [e2, h] <;> decide := hsq
  have hlt : n % 12 < 12 := Nat.mod_lt (n) (by norm_num)
  have hn12 : n % 12 = 0 ∨ n % 12 = 1 ∨ n % 12 = 2 ∨ n % 12 = 3 ∨ n % 12 = 4 ∨ n % 12 = 5 ∨ n % 12 =
    6 ∨ n % 12 = 7 ∨ n % 12 = 8 ∨ n % 12 = 9 ∨ n % 12 = 10 ∨ n % 12 = 11 := by omega
  obtain h | h | h | h | h | h | h | h | h | h | h | h := hn12
  · exact Or.inl h
  · exfalso; rw [h] at hper
    have hRv := hper.symm.trans hL
    obtain h2 | h2 <;> rw [h2] at hRv <;> revert hRv <;> decide := h28
  · exfalso; rw [h] at hper
    have hRv := hper.symm.trans hL
    obtain h2 | h2 <;> rw [h2] at hRv <;> revert hRv <;> decide := h28
  · exfalso; rw [h] at hper
    have hRv := hper.symm.trans hL
    obtain h2 | h2 <;> rw [h2] at hRv <;> revert hRv <;> decide := h28
  · exfalso; rw [h] at hper
    have hRv := hper.symm.trans hL
    obtain h2 | h2 <;> rw [h2] at hRv <;> revert hRv <;> decide := h28
  · exfalso; rw [h] at hper
    have hRv := hper.symm.trans hL
    obtain h2 | h2 <;> rw [h2] at hRv <;> revert hRv <;> decide := h28
  · exact Or.inr h
  · exfalso; rw [h] at hper
    have hRv := hper.symm.trans hL
    obtain h2 | h2 <;> rw [h2] at hRv <;> revert hRv <;> decide := h28
  · exfalso; rw [h] at hper
    have hRv := hper.symm.trans hL
    obtain h2 | h2 <;> rw [h2] at hRv <;> revert hRv <;> decide := h28
  · exfalso; rw [h] at hper
    have hRv := hper.symm.trans hL
    obtain h2 | h2 <;> rw [h2] at hRv <;> revert hRv <;> decide := h28
  · exfalso; rw [h] at hper
    have hRv := hper.symm.trans hL
    obtain h2 | h2 <;> rw [h2] at hRv <;> revert hRv <;> decide := h28
  · exfalso; rw [h] at hper
    have hRv := hper.symm.trans hL
    obtain h2 | h2 <;> rw [h2] at hRv <;> revert hRv <;> decide := h28

end MetaMathlibExt

namespace MetaMathlibExt

/--
[jacobi_contra](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma jacobi_contra (b c : ℕ) (x : ℤ) (hodd : Odd b) (hmod : b % 4 = 3)
  (hgc : Int.gcd (c : ℤ) (b : ℤ) = 1)
  (hdvd : (b : ℤ) ∣ 2 * (x ^ 2 + (c : ℤ) ^ 2)) : False := by
  have h2b : ¬ 2 ∣ b := by
    rintro ⟨t, ht⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcb2 : Nat.Coprime 2 b := (Nat.prime_two.coprime_iff_not_dvd).mpr h2b
  have hiso : IsCoprime ((b : ℕ) : ℤ) (2 : ℤ) := by
    have h := hcb2.symm.isCoprime
    simpa using h
  have h1 : (b : ℤ) ∣ x ^ 2 + (c : ℤ) ^ 2 := hiso.dvd_of_dvd_mul_left hdvd
  have hmodEq : x ^ 2 ≡ -((c : ℤ) ^ 2) [ZMOD (b : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have e : (-((c : ℤ) ^ 2)) - x ^ 2 = -(x ^ 2 + (c : ℤ) ^ 2) := by ring
    rw [e]
    exact dvd_neg.mpr h1
  have heq : x ^ 2 % ((b : ℕ) : ℤ) = -((c : ℤ) ^ 2) % ((b : ℕ) : ℤ) := hmodEq.eq
  have hJeq : jacobiSym (x ^ 2) b = jacobiSym (-((c : ℤ) ^ 2)) b := jacobiSym.mod_left' heq
  have hRHS : jacobiSym (-((c : ℤ) ^ 2)) b = -1 := by
    have e : (-((c : ℤ) ^ 2)) = (-1) * (c : ℤ) ^ 2 := by ring
    rw [e, jacobiSym.mul_left, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four hmod,
      jacobiSym.sq_one' hgc, mul_one]
  have hLHS : jacobiSym (x ^ 2) b = 0 ∨ jacobiSym (x ^ 2) b = 1 := by
    have e2 : jacobiSym (x ^ 2) b = jacobiSym x b ^ 2 := jacobiSym.pow_left x 2 b
    rw [e2]
    obtain h | h | h <;> rw [h] <;> decide := jacobiSym.trichotomy x b
  rw [hJeq, hRHS] at hLHS
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[case_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma case_zero (n x : ℕ) (hn : 0 < n) (h : lucasNumber n = 2 * x ^ 2)
  (h0 : n % 12 = 0) : False := by
  have hZ : lz n = 2 * (x : ℤ) ^ 2 := by
    change ((lucasNumber n : ℕ) : ℤ) = _
    exact_mod_cast h
  obtain ⟨e, j, hjodd, hnj⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n ≠ 0)
  have h4 : 4 ∣ n := by omega
  have hd4 : 2 ^ 2 ∣ n := h4
  have he2 : 2 ≤ e := valuation_ge n e j 2 hjodd hnj hd4
  obtain ⟨g, rfl⟩ : ∃ g, e = g + 1 := ⟨e - 1, by omega⟩
  have hg1 : 1 ≤ g := by omega
  have epg : 2 ^ (g + 1) = 2 * 2 ^ g := by ring
  have hev : Even (2 ^ g) := even_two_pow g hg1
  have hdiv0 := iterate_dvd (2 ^ g) hev 0 j
  have hjneg : (-1 : ℤ) ^ j = -1 := hjodd.neg_one_pow
  have hn_idx : 0 + 2 * (2 ^ g) * j = n := by
    have e3 : 2 * (2 ^ g) * j = 2 ^ (g + 1) * j := by rw [epg]
    omega
  rw [hn_idx, hjneg, lz_zero] at hdiv0
  have hfin : lz (2 ^ g) ∣ 2 * ((x : ℤ) ^ 2 + (((1 : ℕ)) : ℤ) ^ 2) := by
    have e : (2 : ℤ) * ((x : ℤ) ^ 2 + (((1 : ℕ)) : ℤ) ^ 2) = lz n - -1 * 2 := by
      rw [hZ]; ring
    rwa [e]
  have hodd := (pow2_odd_mod4 g hg1).1
  have hmod := (pow2_odd_mod4 g hg1).2
  have hgc : Int.gcd (((1 : ℕ)) : ℤ) (((lucasNumber (2 ^ g))) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast, Nat.gcd_one_left]
  exact jacobi_contra (lucasNumber (2 ^ g)) 1 (x : ℤ) hodd hmod hgc hfin

end MetaMathlibExt

namespace MetaMathlibExt

/--
[case_six_a](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma case_six_a (n x : ℕ) (h : lucasNumber n = 2 * x ^ 2)
  (h24 : n % 24 = 6) (hn6 : n ≠ 6) : False := by
  have hZ : lz n = 2 * (x : ℤ) ^ 2 := by
    change ((lucasNumber n : ℕ) : ℤ) = _
    exact_mod_cast h
  have h86 : 8 ∣ n - 6 := by omega
  have hne : n - 6 ≠ 0 := by omega
  obtain ⟨f, j, hjodd, hnj⟩ := Nat.exists_eq_two_pow_mul_odd hne
  have hd8 : 2 ^ 3 ∣ n - 6 := h86
  have hf3 : 3 ≤ f := valuation_ge (n - 6) f j 3 hjodd hnj hd8
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hg2 : 2 ≤ g := by omega
  have epg : 2 ^ (g + 1) = 2 * 2 ^ g := by ring
  have hev : Even (2 ^ g) := even_two_pow g (by omega)
  have hdiv0 := iterate_dvd (2 ^ g) hev 6 j
  have hjneg : (-1 : ℤ) ^ j = -1 := hjodd.neg_one_pow
  have hn_idx : 6 + 2 * (2 ^ g) * j = n := by
    have e3 : 2 * (2 ^ g) * j = 2 ^ (g + 1) * j := by rw [epg]
    omega
  rw [hn_idx, hjneg, lz_six] at hdiv0
  have hfin : lz (2 ^ g) ∣ 2 * ((x : ℤ) ^ 2 + (((3 : ℕ)) : ℤ) ^ 2) := by
    have e : (2 : ℤ) * ((x : ℤ) ^ 2 + (((3 : ℕ)) : ℤ) ^ 2) = lz n - -1 * 18 := by
      rw [hZ]; ring
    rwa [e]
  have hodd := (pow2_odd_mod4 g (by omega)).1
  have hmod := (pow2_odd_mod4 g (by omega)).2
  have h3 : ¬ 3 ∣ lucasNumber (2 ^ g) := pow2_not3dvd g hg2
  have hgc : Int.gcd (((3 : ℕ)) : ℤ) (((lucasNumber (2 ^ g))) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    have hcop : Nat.Coprime 3 (lucasNumber (2 ^ g)) :=
      (Nat.prime_three.coprime_iff_not_dvd).mpr h3
    have h1 : Nat.gcd 3 (lucasNumber (2 ^ g)) = 1 := hcop
    exact_mod_cast h1
  exact jacobi_contra (lucasNumber (2 ^ g)) 3 (x : ℤ) hodd hmod hgc hfin

end MetaMathlibExt

namespace MetaMathlibExt

/--
[case_six_b](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
private lemma case_six_b (n x : ℕ) (h : lucasNumber n = 2 * x ^ 2)
  (h24 : n % 24 = 18) : False := by
  have hZ : lz n = 2 * (x : ℤ) ^ 2 := by
    change ((lucasNumber n : ℕ) : ℤ) = _
    exact_mod_cast h
  have h86 : 8 ∣ n + 6 := by omega
  obtain ⟨f, j, hjodd, hnj⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : n + 6 ≠ 0)
  have hd8 : 2 ^ 3 ∣ n + 6 := h86
  have hf3 : 3 ≤ f := valuation_ge (n + 6) f j 3 hjodd hnj hd8
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hg2 : 2 ≤ g := by omega
  have epg : 2 ^ (g + 1) = 2 * 2 ^ g := by ring
  have hev : Even (2 ^ g) := even_two_pow g (by omega)
  have hk4 : 4 ≤ 2 ^ g := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (show 2 ≤ g by omega)
    norm_num at h
    exact h
  have hj1 : 1 ≤ j := hjodd.pos
  obtain ⟨t, ht⟩ := hjodd
  have hevj1 : Even (j - 1) := ⟨t, by omega⟩
  have hjj : (-1 : ℤ) ^ (j - 1) = 1 := hevj1.neg_one_pow
  have hn_idx : (2 * (2 ^ g) - 6) + 2 * (2 ^ g) * (j - 1) = n := by
    have e3 : 2 * (2 ^ g) * (j - 1) = 2 ^ (g + 1) * (j - 1) := by rw [epg]
    have hjj1 : j = (j - 1) + 1 := by omega
    have e4 : 2 ^ (g + 1) * j = 2 ^ (g + 1) * (j - 1) + 2 ^ (g + 1) := by
      conv_lhs => rw [hjj1]
      rw [Nat.mul_add, Nat.mul_one]
    omega
  have hdiv0 := iterate_dvd (2 ^ g) hev (2 * (2 ^ g) - 6) (j - 1)
  rw [hn_idx, hjj] at hdiv0
  have hrefl : lz (2 ^ g) ∣ lz (2 * (2 ^ g) - 6) + 18 := by
    by_cases hg2' : g = 2
    · subst hg2'
      decide
    · have hg3 : 3 ≤ g := by omega
      have hk8 : 8 ≤ 2 ^ g := by
        have h := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (show 3 ≤ g by omega)
        norm_num at h
        exact h
      have hk6 : 6 ≤ 2 ^ g := by omega
      have hadd := add_identity ((2 ^ g) - 6) 6
      have f1 : 6 + 2 * ((2 ^ g) - 6) = 2 * (2 ^ g) - 6 := by omega
      have f2 : 6 + ((2 ^ g) - 6) = 2 ^ g := by omega
      obtain ⟨r, hr⟩ := hev
      have hev' : Even ((2 ^ g) - 6) := ⟨r - 3, by omega⟩
      have hsign : (-1 : ℤ) ^ ((2 ^ g) - 6) = 1 := hev'.neg_one_pow
      rw [f1, f2, hsign, lz_six] at hadd
      have e : lz (2 * (2 ^ g) - 6) + 18 = lz (2 ^ g) * lz ((2 ^ g) - 6) := by
        linear_combination hadd
      rw [e]
      exact dvd_mul_right _ _
  have hfin : lz (2 ^ g) ∣ 2 * ((x : ℤ) ^ 2 + (((3 : ℕ)) : ℤ) ^ 2) := by
    have e : (2 : ℤ) * ((x : ℤ) ^ 2 + (((3 : ℕ)) : ℤ) ^ 2) =
      (lz n - 1 * lz (2 * (2 ^ g) - 6)) + (lz (2 * (2 ^ g) - 6) + 18) := by
      rw [hZ]; ring
    rw [e]
    exact dvd_add hdiv0 hrefl
  have hodd := (pow2_odd_mod4 g (by omega)).1
  have hmod := (pow2_odd_mod4 g (by omega)).2
  have h3 : ¬ 3 ∣ lucasNumber (2 ^ g) := pow2_not3dvd g hg2
  have hgc : Int.gcd (((3 : ℕ)) : ℤ) (((lucasNumber (2 ^ g))) : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    have hcop : Nat.Coprime 3 (lucasNumber (2 ^ g)) :=
      (Nat.prime_three.coprime_iff_not_dvd).mpr h3
    have h1 : Nat.gcd 3 (lucasNumber (2 ^ g)) = 1 := hcop
    exact_mod_cast h1
  exact jacobi_contra (lucasNumber (2 ^ g)) 3 (x : ℤ) hodd hmod hgc hfin

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cohn_twice_square_lucas](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareLucas.lean)
-/
@[path]
lemma cohn_twice_square_lucas
  {n x : ℕ}
-- given
  (hn : 0 < n)
  (h : lucasNumber n = 2 * x ^ 2) :
-- imply
  n = 6 := by
-- proof
  have hcases := mod12_cases n x h
  obtain h0 | h6 := hcases
  · exfalso
    exact case_zero n x hn h h0
  · by_cases hn6 : n = 6
    · exact hn6
    · have h24 : n % 24 = 6 ∨ n % 24 = 18 := by omega
      obtain h24a | h24b := h24
      · exfalso
        exact case_six_a n x h h24a hn6
      · exfalso
        exact case_six_b n x h h24b
end



-- created on 2026-10-20
-- updated on 2026-10-23
