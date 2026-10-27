import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[pocklington_exponent_arithmetic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PocklingtonPrimePowerCriterion.lean)
-/
@[path]
private lemma pocklington_exponent_arithmetic (N K p e : ℕ)
  (hKpos : 0 < K) (hp : Nat.Prime p)
  (hN : N = K * p ^ e + 1) (hlt : K < p ^ e) :
  0 < e ∧ 2 ≤ N ∧ N - 1 = K * p ^ e ∧
    (N - 1) / p = K * p ^ (e - 1) := by
  have he : 0 < e := by
    by_contra he
    have : e = 0 := Nat.eq_zero_of_not_pos he
    subst e
    simp only [pow_zero] at hlt
    omega
  have hpowpos : 0 < p ^ e := Nat.pow_pos hp.pos
  have hNge : 2 ≤ N := by
    rw [hN]
    have : 0 < K * p ^ e := Nat.mul_pos hKpos hpowpos
    omega
  have hNm1 : N - 1 = K * p ^ e := by omega
  refine ⟨he, hNge, hNm1, ?_⟩
  rw [hNm1, show e = e - 1 + 1 by omega, pow_succ, ← mul_assoc]
  exact Nat.mul_div_cancel _ hp.pos

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pocklington_reduced_power_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PocklingtonPrimePowerCriterion.lean)
-/
@[path]
private lemma pocklington_reduced_power_ne_one (N p a q : ℕ)
  (hqPrime : Nat.Prime q) (hqN : q ∣ N)
  (hgcd : Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
  (a : ZMod q) ^ ((N - 1) / p) ≠ 1 := by
  intro hpow
  have hcast : (↑(a ^ ((N - 1) / p)) : ZMod q) = (1 : ℕ) := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hpow
  have hmod : Nat.ModEq q (a ^ ((N - 1) / p)) 1 :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hqSub : q ∣ a ^ ((N - 1) / p) - 1 := hmod.symm.dvd'
  have hqGcd : q ∣ Nat.gcd (a ^ ((N - 1) / p) - 1) N := Nat.dvd_gcd hqSub hqN
  rw [hgcd] at hqGcd
  exact hqPrime.ne_one (Nat.dvd_one.mp hqGcd)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pocklington_prime_power_dvd_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PocklingtonPrimePowerCriterion.lean)
-/
@[path]
private lemma pocklington_prime_power_dvd_sub_one (N K p e a q : ℕ)
  (hp : Nat.Prime p) (he : 0 < e)
  (hqPrime : Nat.Prime q) (hqN : q ∣ N)
  (hNm1 : N - 1 = K * p ^ e)
  (hdiv : (N - 1) / p = K * p ^ (e - 1))
  (hmod : Nat.ModEq N (a ^ (N - 1)) 1)
  (hgcd : Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
  p ^ e ∣ q - 1 := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let _ : Fact (Nat.Prime q) := ⟨hqPrime⟩
  have hfullA : (a : ZMod q) ^ (N - 1) = 1 := by
    have hcast : (↑(a ^ (N - 1)) : ZMod q) = (1 : ℕ) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.ModEq.of_dvd hqN hmod)
    simpa only [Nat.cast_pow, Nat.cast_one] using hcast
  have hnotA : (a : ZMod q) ^ ((N - 1) / p) ≠ 1 :=
    pocklington_reduced_power_ne_one N p a q hqPrime hqN hgcd
  let y : ZMod q := (a : ZMod q) ^ K
  have hfullY : y ^ (p ^ e) = 1 := by
    change ((a : ZMod q) ^ K) ^ (p ^ e) = 1
    rwa [← pow_mul, ← hNm1]
  have hnotY : y ^ (p ^ (e - 1)) ≠ 1 := by
    simpa only [hdiv, pow_mul, y] using hnotA
  have hpred : e - 1 + 1 = e := by omega
  have horder : orderOf y = p ^ e := by
    have horder' := orderOf_eq_prime_pow hnotY (by
      rw [hpred]
      exact hfullY)
    simpa only [hpred] using horder'
  have hy0 : y ≠ 0 := by
    intro hy0
    rw [hy0, zero_pow (Nat.pow_pos hp.pos).ne'] at hfullY
    exact zero_ne_one hfullY
  rw [← horder]
  exact ZMod.orderOf_dvd_card_sub_one hy0

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pocklington_prime_divisor_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PocklingtonPrimePowerCriterion.lean)
-/
@[path]
private lemma pocklington_prime_divisor_lower_bound (N K p e a q : ℕ)
  (hp : Nat.Prime p) (he : 0 < e)
  (hqPrime : Nat.Prime q) (hqN : q ∣ N)
  (hNm1 : N - 1 = K * p ^ e)
  (hdiv : (N - 1) / p = K * p ^ (e - 1))
  (hmod : Nat.ModEq N (a ^ (N - 1)) 1)
  (hgcd : Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
  p ^ e + 1 ≤ q := by
  have hdvd := pocklington_prime_power_dvd_sub_one N K p e a q hp he hqPrime hqN
    hNm1 hdiv hmod hgcd
  have hqTwo := hqPrime.two_le
  have hqSub : 0 < q - 1 := by omega
  have hle := Nat.le_of_dvd hqSub hdvd
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pocklington_factor_bound_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PocklingtonPrimePowerCriterion.lean)
-/
@[path]
private lemma pocklington_factor_bound_contradiction (N K p e q : ℕ)
  (hp : Nat.Prime p) (hN : N = K * p ^ e + 1) (hlt : K < p ^ e)
  (hqLower : p ^ e + 1 ≤ q) (hqSq : q ^ 2 ≤ N) : False := by
  have hLowerSq : (p ^ e + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hqLower 2
  have hpowPos : 0 < p ^ e := Nat.pow_pos hp.pos
  have hmulLt : K * p ^ e < p ^ e * p ^ e :=
    (Nat.mul_lt_mul_right hpowPos).2 hlt
  have hNlt : N < (p ^ e) ^ 2 + 1 := by
    rw [hN, pow_two]
    omega
  have hsqGap : (p ^ e) ^ 2 + 1 < (p ^ e + 1) ^ 2 := by
    nlinarith
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pocklington_prime_power_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PocklingtonPrimePowerCriterion.lean)
-/
@[path]
lemma pocklington_prime_power_criterion
  {N K p e : ℕ}
-- given
  (hKpos : 0 < K)
  (hp : Nat.Prime p)
  (hN : N = K * p ^ e + 1)
  (hlt : K < p ^ e)
  (hex : ∃ a : ℕ, Nat.ModEq N (a ^ (N - 1)) 1 ∧ Nat.gcd (a ^ ((N - 1) / p) - 1) N = 1) :
-- imply
  Nat.Prime N := by
-- proof
  obtain ⟨he, hNge, hNm1, hdiv⟩ :=
    pocklington_exponent_arithmetic N K p e hKpos hp hN hlt
  obtain ⟨a, hmod, hgcd⟩ := hex
  by_contra hComposite
  let q := N.minFac
  have hqPrime : Nat.Prime q := Nat.minFac_prime (by omega)
  have hqN : q ∣ N := Nat.minFac_dvd N
  have hqLower := pocklington_prime_divisor_lower_bound N K p e a q hp he hqPrime hqN
    hNm1 hdiv hmod hgcd
  have hqSq : q ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hComposite
  exact pocklington_factor_bound_contradiction N K p e q hp hN hlt hqLower hqSq

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
