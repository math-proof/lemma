import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[proth_arithmetic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProthTheorem.lean)
-/
@[path]
private lemma proth_arithmetic (h k N : ℕ) (hOdd : Odd h) (hlt : h < 2 ^ k)
  (hN : N = h * 2 ^ k + 1) :
  0 < h ∧ 0 < k ∧ 3 ≤ N ∧ Odd N ∧
    (N - 1) / 2 = h * 2 ^ (k - 1) ∧ (N - 1) / 2 = N / 2 := by
  have hh : 0 < h := hOdd.pos
  have hk : 0 < k := by
    by_contra hk
    have : k = 0 := by omega
    subst k
    simp only [pow_zero] at hlt
    omega
  have hrepr : N = 2 * (h * 2 ^ (k - 1)) + 1 := by
    calc
      N = h * 2 ^ k + 1 := hN
      _ = 2 * (h * 2 ^ (k - 1)) + 1 := by
        rw [← Nat.two_pow_pred_mul_two hk]
        ring
  have ht : 0 < h * 2 ^ (k - 1) := Nat.mul_pos hh (Nat.pow_pos (by omega))
  have hNodd : Odd N := by
    rw [hrepr]
    exact (even_two_mul _).add_one
  refine ⟨hh, hk, by omega, hNodd, ?_, ?_⟩ <;> omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[proth_prime_witness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProthTheorem.lean)
-/
@[path]
private lemma proth_prime_witness (N : ℕ) (hPrime : Nat.Prime N) (hNtwo : N ≠ 2) :
  ∃ a : ZMod N, a ^ (N / 2) = -1 := by
  let _ : Fact (Nat.Prime N) := ⟨hPrime⟩
  have hChar : ringChar (ZMod N) ≠ 2 := by
    rwa [ZMod.ringChar_zmod_n]
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hChar
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    exact ha IsSquare.zero
  refine ⟨a, ?_⟩
  obtain hone | hneg := ZMod.pow_div_two_eq_neg_one_or_one N ha0
  · exact (ha ((ZMod.euler_criterion N ha0).2 hone)).elim
  · exact hneg

end MetaMathlibExt

namespace MetaMathlibExt

/--
[proth_orderOf_eq_two_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProthTheorem.lean)
-/
@[path]
private lemma proth_orderOf_eq_two_pow {R : Type*} [Ring R] [Nontrivial R]
  (x : R) (k : ℕ) (hk : 0 < k) (hChar : ringChar R ≠ 2)
  (hhalf : x ^ (2 ^ (k - 1)) = -1) : orderOf x = 2 ^ k := by
  have hnot : ¬orderOf x ∣ 2 ^ (k - 1) := by
    rw [orderOf_dvd_iff_pow_eq_one]
    intro hone
    exact Ring.neg_one_ne_one_of_char_ne_two hChar (hhalf.symm.trans hone)
  have hfull : x ^ (2 ^ k) = 1 := by
    rw [← Nat.two_pow_pred_mul_two hk, pow_mul, hhalf]
    simp
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hfull
  have hk' : k - 1 + 1 = k := by omega
  have horder : orderOf x = 2 ^ (k - 1 + 1) :=
    Nat.eq_prime_pow_of_dvd_least_prime_pow Nat.prime_two hnot (by simpa only [hk'])
  simpa only [hk'] using horder

end MetaMathlibExt

namespace MetaMathlibExt

/--
[proth_two_pow_dvd_orderOf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProthTheorem.lean)
-/
@[path]
private lemma proth_two_pow_dvd_orderOf {R : Type*} [Ring R] [Nontrivial R]
  (b : R) (h k : ℕ) (hk : 0 < k) (hChar : ringChar R ≠ 2)
  (hhalf : b ^ (h * 2 ^ (k - 1)) = -1) : 2 ^ k ∣ orderOf b := by
  have hxhalf : (b ^ h) ^ (2 ^ (k - 1)) = -1 := by
    rwa [← pow_mul]
  have horder := proth_orderOf_eq_two_pow (b ^ h) k hk hChar hxhalf
  rw [← horder]
  exact orderOf_pow_dvd h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[proth_two_pow_dvd_prime_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProthTheorem.lean)
-/
@[path]
private lemma proth_two_pow_dvd_prime_sub_one (h k N q : ℕ) (hh : 0 < h)
  (hk : 0 < k) (hNodd : Odd N) (hqPrime : Nat.Prime q) (hqN : q ∣ N)
  (a : ZMod N) (ha : a ^ (h * 2 ^ (k - 1)) = -1) : 2 ^ k ∣ q - 1 := by
  let _ : Fact (Nat.Prime q) := ⟨hqPrime⟩
  have hq2 : q ≠ 2 := by
    intro hq2
    subst q
    exact hNodd.not_two_dvd_nat hqN
  have hChar : ringChar (ZMod q) ≠ 2 := by
    rwa [ZMod.ringChar_zmod_n]
  let b : ZMod q := ZMod.castHom hqN (ZMod q) a
  have hbhalf : b ^ (h * 2 ^ (k - 1)) = -1 := by
    simpa only [b, map_pow, map_neg, map_one] using
      congrArg (ZMod.castHom hqN (ZMod q)) ha
  have hexp : 0 < h * 2 ^ (k - 1) := Nat.mul_pos hh (Nat.pow_pos (by omega))
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0, zero_pow hexp.ne'] at hbhalf
    exact (neg_ne_zero.mpr one_ne_zero) hbhalf.symm
  exact (proth_two_pow_dvd_orderOf b h k hk hChar hbhalf).trans
    (ZMod.orderOf_dvd_card_sub_one hb0)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[proth_prime_divisor_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProthTheorem.lean)
-/
@[path]
private lemma proth_prime_divisor_lower_bound (h k N q : ℕ) (hh : 0 < h)
  (hk : 0 < k) (hNodd : Odd N) (hqPrime : Nat.Prime q) (hqN : q ∣ N)
  (a : ZMod N) (ha : a ^ (h * 2 ^ (k - 1)) = -1) : 2 ^ k + 1 ≤ q := by
  have hdvd := proth_two_pow_dvd_prime_sub_one h k N q hh hk hNodd hqPrime hqN a ha
  have hqTwo := hqPrime.two_le
  have hqSub : 0 < q - 1 := by omega
  have hle := Nat.le_of_dvd hqSub hdvd
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[proth_composite_impossible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProthTheorem.lean)
-/
@[path]
private lemma proth_composite_impossible (h k N : ℕ) (hh : 0 < h) (hk : 0 < k)
  (hNge : 3 ≤ N) (hNodd : Odd N) (hlt : h < 2 ^ k) (hN : N = h * 2 ^ k + 1)
  (a : ZMod N) (ha : a ^ (h * 2 ^ (k - 1)) = -1) (hComposite : ¬Nat.Prime N) : False := by
  let q := N.minFac
  have hqPrime : Nat.Prime q := Nat.minFac_prime (by omega)
  have hqN : q ∣ N := Nat.minFac_dvd N
  have hqLower :=
    proth_prime_divisor_lower_bound h k N q hh hk hNodd hqPrime hqN a ha
  have hqSq : q ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hComposite
  have hLowerSq : (2 ^ k + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hqLower 2
  have hpowPos : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have hmulLt : h * 2 ^ k < 2 ^ k * 2 ^ k :=
    (Nat.mul_lt_mul_right hpowPos).2 hlt
  have hNlt : N < (2 ^ k) ^ 2 + 1 := by
    rw [hN, pow_two]
    omega
  have hsqGap : (2 ^ k) ^ 2 + 1 < (2 ^ k + 1) ^ 2 := by
    nlinarith
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[proth_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProthTheorem.lean)
-/
@[path]
lemma proth_theorem
  {h k N : ℕ}
-- given
  (hOdd : Odd h)
  (hlt : h < 2 ^ k)
  (hN : N = h * 2 ^ k + 1) :
-- imply
  Nat.Prime N ↔ ∃ a : ZMod N, a ^ ((N - 1) / 2) = -1 := by
-- proof
  obtain ⟨hh, hk, hNge, hNodd, hexp, hhalf⟩ := proth_arithmetic h k N hOdd hlt hN
  constructor
  · intro hPrime
    obtain ⟨a, ha⟩ := proth_prime_witness N hPrime (by omega)
    refine ⟨a, ?_⟩
    rwa [hhalf]
  · rintro ⟨a, ha⟩
    by_contra hComposite
    exact proth_composite_impossible h k N hh hk hNge hNodd hlt hN a (by
      rw [← hexp]
      exact ha) hComposite

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
