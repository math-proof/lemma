import Mathlib
import Initialize.Tactic.Attr.Basic


namespace Nat

/--
[fermatNumber_mod_prime_exact_preperiod_period](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatResiduePeriod.lean)
-/
@[path]
lemma fermatNumber_mod_prime_exact_preperiod_period
  {p v w : ℕ}
-- given
  (hp : p.Prime)
  (hp2 : p ≠ 2)
  (hord : orderOf (2 : ZMod p) = 2 ^ v * w)
  (hw : Odd w) :
-- imply
  let k := orderOf (2 : ZMod w)
  Function.Periodic (fun n : ℕ => ((Nat.fermatNumber (v + n) : ℕ) : ZMod p)) k ∧
    (∀ h < v, ¬∃ kp : ℕ, 0 < kp ∧
      Function.Periodic (fun n : ℕ => ((Nat.fermatNumber (h + n) : ℕ) : ZMod p)) kp) ∧
    ∀ kp : ℕ, 0 < kp →
      Function.Periodic (fun n : ℕ => ((Nat.fermatNumber (v + n) : ℕ) : ZMod p)) kp →
        k ∣ kp := by
-- proof
  have hwpos : 0 < w := hw.pos
  have _neW : NeZero w := ⟨hwpos.ne'⟩
  have _factP : Fact p.Prime := ⟨hp⟩
  have _neP : NeZero p := ⟨hp.pos.ne'⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hcon
    have hc : ((2 : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by simpa using hcon
    have hmod : 2 ≡ 0 [MOD p] := (ZMod.natCast_eq_natCast_iff 2 0 p).mp hc
    have hdvd : p ∣ 2 := Nat.modEq_zero_iff_dvd.mp hmod
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := hp.two_le
    exact hp2 (le_antisymm hle hge)
  have hunit2p : IsUnit (2 : ZMod p) := isUnit_iff_ne_zero.mpr h2ne
  have hfin2p : IsOfFinOrder (2 : ZMod p) := hunit2p.isOfFinOrder
  have hunit2w : IsUnit (2 : ZMod w) := by
    have h := (ZMod.isUnit_iff_coprime 2 w).mpr hw.coprime_two_left
    simpa using h
  have hF : ∀ n : ℕ, ((Nat.fermatNumber n : ℕ) : ZMod p)
    = (2 : ZMod p) ^ (2 ^ n) + 1 := by
    intro n
    have e : Nat.fermatNumber n = 2 ^ 2 ^ n + 1 := rfl
    rw [e]
    simp
  have hk1 : (2 : ZMod w) ^ orderOf (2 : ZMod w) = 1 := pow_orderOf_eq_one _
  have h2kcast : ((2 ^ orderOf (2 : ZMod w) : ℕ) : ZMod w) = ((1 : ℕ) : ZMod w) := by
    have c1 : ((2 ^ orderOf (2 : ZMod w) : ℕ) : ZMod w)
      = (2 : ZMod w) ^ orderOf (2 : ZMod w) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    rw [c1, hk1, Nat.cast_one]
  have hmodk : 2 ^ orderOf (2 : ZMod w) ≡ 1 [MOD w] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp h2kcast
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have hmodt : 2 ^ (n + orderOf (2 : ZMod w)) ≡ 2 ^ n [MOD w] := by
      have h1 : 2 ^ (n + orderOf (2 : ZMod w)) = 2 ^ n * 2 ^ orderOf (2 : ZMod w) :=
        pow_add 2 n _
      rw [h1]
      have h2 := Nat.ModEq.mul_left (2 ^ n) hmodk
      rwa [mul_one] at h2
    have hle : 2 ^ n ≤ 2 ^ (n + orderOf (2 : ZMod w)) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right n _)
    have hdvd : w ∣ 2 ^ (n + orderOf (2 : ZMod w)) - 2 ^ n :=
      (Nat.modEq_iff_dvd' hle).mp hmodt.symm
    have e1 : 2 ^ (v + (n + orderOf (2 : ZMod w)))
      = 2 ^ v * 2 ^ (n + orderOf (2 : ZMod w)) := pow_add 2 v _
    have e2 : 2 ^ (v + n) = 2 ^ v * 2 ^ n := pow_add 2 v n
    have hleV : 2 ^ (v + n) ≤ 2 ^ (v + (n + orderOf (2 : ZMod w))) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_left (Nat.le_add_right n _) v)
    have hdvdV : 2 ^ v * w ∣ 2 ^ (v + (n + orderOf (2 : ZMod w))) - 2 ^ (v + n) := by
      have hmul : 2 ^ v * w ∣ 2 ^ v * (2 ^ (n + orderOf (2 : ZMod w)) - 2 ^ n) :=
        Nat.mul_dvd_mul_left _ hdvd
      have heq : 2 ^ v * (2 ^ (n + orderOf (2 : ZMod w)) - 2 ^ n)
        = 2 ^ (v + (n + orderOf (2 : ZMod w))) - 2 ^ (v + n) := by
        rw [Nat.mul_sub, e1, e2]
      rwa [heq] at hmul
    have hmodV : 2 ^ (v + n) ≡ 2 ^ (v + (n + orderOf (2 : ZMod w))) [MOD 2 ^ v * w] :=
      (Nat.modEq_iff_dvd' hleV).mpr hdvdV
    rw [← hord] at hmodV
    have hpow : (2 : ZMod p) ^ (2 ^ (v + n))
      = (2 : ZMod p) ^ (2 ^ (v + (n + orderOf (2 : ZMod w)))) :=
      hfin2p.pow_eq_pow_iff_modEq.mpr hmodV
    show ((Nat.fermatNumber (v + (n + orderOf (2 : ZMod w))) : ℕ) : ZMod p)
      = ((Nat.fermatNumber (v + n) : ℕ) : ZMod p)
    rw [hF, hF, hpow]
  · intro h hhv
    rintro ⟨kp, hkppos, hper⟩
    have h0 := hper 0
    simp only [zero_add, add_zero] at h0
    have hF0 : (2 : ZMod p) ^ (2 ^ (h + kp)) = (2 : ZMod p) ^ (2 ^ h) := by
      have h00 : (2 : ZMod p) ^ (2 ^ (h + kp)) + 1 = (2 : ZMod p) ^ (2 ^ h) + 1 := by
        rwa [← hF (h + kp), ← hF h]
      exact add_right_cancel_iff.mp h00
    have hmod0 : 2 ^ (h + kp) ≡ 2 ^ h [MOD orderOf (2 : ZMod p)] :=
      hfin2p.pow_eq_pow_iff_modEq.mp hF0
    rw [hord] at hmod0
    have hle : 2 ^ h ≤ 2 ^ (h + kp) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right h kp)
    have hdvd : 2 ^ v * w ∣ 2 ^ (h + kp) - 2 ^ h :=
      (Nat.modEq_iff_dvd' hle).mp hmod0.symm
    have e1 : 2 ^ (h + kp) = 2 ^ h * 2 ^ kp := pow_add 2 h kp
    have efac : 2 ^ (h + kp) - 2 ^ h = 2 ^ h * (2 ^ kp - 1) := by
      rw [e1, Nat.mul_sub, mul_one]
    rw [efac] at hdvd
    have e2 : 2 ^ h * 2 ^ (v - h) = 2 ^ v := by rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hhv)]
    rw [← e2, mul_assoc] at hdvd
    have hdvd2 : 2 ^ (v - h) * w ∣ 2 ^ kp - 1 :=
      (Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num : 0 < 2) h)).mp hdvd
    have hvh : 0 < v - h := Nat.sub_pos_of_lt hhv
    have h2dvd : 2 ∣ 2 ^ (v - h) := dvd_pow_self 2 hvh.ne'
    have h2dvdM : 2 ∣ 2 ^ kp - 1 := (h2dvd.mul_right w).trans hdvd2
    have hE : Even (2 ^ kp) := even_iff_two_dvd.mpr (dvd_pow_self 2 hkppos.ne')
    have hO : Odd (2 ^ kp - 1) := Nat.Even.sub_odd Nat.one_le_two_pow hE odd_one
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h2dvdM)
  · intro kp hkppos hper
    have h0 := hper 0
    simp only [zero_add, add_zero] at h0
    have hF0 : (2 : ZMod p) ^ (2 ^ (v + kp)) = (2 : ZMod p) ^ (2 ^ v) := by
      have h00 : (2 : ZMod p) ^ (2 ^ (v + kp)) + 1 = (2 : ZMod p) ^ (2 ^ v) + 1 := by
        rwa [← hF (v + kp), ← hF v]
      exact add_right_cancel_iff.mp h00
    have hmod0 : 2 ^ (v + kp) ≡ 2 ^ v [MOD orderOf (2 : ZMod p)] :=
      hfin2p.pow_eq_pow_iff_modEq.mp hF0
    rw [hord] at hmod0
    have hle : 2 ^ v ≤ 2 ^ (v + kp) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right v kp)
    have hdvd : 2 ^ v * w ∣ 2 ^ (v + kp) - 2 ^ v :=
      (Nat.modEq_iff_dvd' hle).mp hmod0.symm
    have e1 : 2 ^ (v + kp) = 2 ^ v * 2 ^ kp := pow_add 2 v kp
    have efac : 2 ^ (v + kp) - 2 ^ v = 2 ^ v * (2 ^ kp - 1) := by
      rw [e1, Nat.mul_sub, mul_one]
    rw [efac] at hdvd
    have hdvd2 : w ∣ 2 ^ kp - 1 :=
      (Nat.mul_dvd_mul_iff_left (pow_pos (by norm_num : 0 < 2) v)).mp hdvd
    have hkp1 : (2 : ZMod w) ^ kp = 1 := by
      obtain ⟨c, hc⟩ := hdvd2
      have hge : 1 ≤ 2 ^ kp := Nat.one_le_two_pow
      have e : 2 ^ kp = w * c + 1 := by omega
      have c1 : ((2 ^ kp : ℕ) : ZMod w) = (2 : ZMod w) ^ kp := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
      have c2 : ((w * c + 1 : ℕ) : ZMod w) = 1 := by
        rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, Nat.cast_one, zero_mul,
          zero_add]
      have heq : ((2 ^ kp : ℕ) : ZMod w) = ((w * c + 1 : ℕ) : ZMod w) := by rw [e]
      rw [c1] at heq
      rwa [c2] at heq
    exact orderOf_dvd_of_pow_eq_one hkp1

end Nat


-- created on 2026-10-20
-- updated on 2026-10-26
