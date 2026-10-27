import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma dvd_mul_of_dvd_mul_of_dvd_mul_sub (N B tau c : ℤ) (h1 : N ∣ B * tau) (h2 : N ∣ B * (tau ^ 2 - c)) : N ∣ B * c := (dvd_sub (h1.mul_right tau) h2).trans (dvd_of_eq (by ring))
private lemma twentyFour_dvd_sq_sub_one (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) : 24 ∣ p ^ 2 - 1 := by
  have h2 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have h3 : p % 3 ≠ 0 := fun h => by
    have := hp.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)
    omega
  have key : ∀ r : ℕ, r < 24 → r % 2 = 1 → r % 3 ≠ 0 → r ^ 2 % 24 = 1 := by decide
  have hmod : p ^ 2 % 24 = 1 := by
    rw [Nat.pow_mod]
    refine key (p % 24) (Nat.mod_lt _ (by omega)) (by omega) (by omega)
  omega
private lemma prime_pow_dvd_sq_sub_one (p m : ℕ) (hp : p.Prime) (a1 tau : ℤ) (h1 : IsCoprime a1 (m : ℤ)) (hpm : ¬ p ∣ m) (hC1 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * tau) (hC2 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * (tau ^ 2 - (p : ℤ) ^ 11 * ((p : ℤ) + 1))) (h24 : 24 ∣ p ^ 2 - 1) (l k : ℕ) (hl : l.Prime) (hlk : l ^ k ∣ 24 * m) : l ^ k ∣ p ^ 2 - 1 := by
  if hlm : l ∣ m then
    have hlp : l ≠ p := fun h => hpm (h ▸ hlm)
    have hlkZ : (l : ℤ) ^ k ∣ (24 * m : ℤ) := by exact_mod_cast hlk
    have hA : IsCoprime ((l : ℤ) ^ k) a1 := (h1.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hlm)).symm.pow_left
    have hP : IsCoprime ((l : ℤ) ^ k) ((p : ℤ) ^ 11) := (Nat.Coprime.cast (R := ℤ) ((Nat.coprime_primes hl hp).mpr hlp)).pow
    have hD : (l : ℤ) ^ k ∣ a1 * ((p : ℤ) ^ 11 * (((p : ℤ) - 1) * ((p : ℤ) + 1))) := (dvd_mul_of_dvd_mul_of_dvd_mul_sub _ _ _ _ (hlkZ.trans hC1) (hlkZ.trans hC2)).trans (dvd_of_eq (by ring))
    have hD2 : (l : ℤ) ^ k ∣ ((p : ℤ) - 1) * ((p : ℤ) + 1) := hP.dvd_of_dvd_mul_left (hA.dvd_of_dvd_mul_left hD)
    have hcast : ((p ^ 2 - 1 : ℕ) : ℤ) = ((p : ℤ) - 1) * ((p : ℤ) + 1) := by
      rw [Nat.cast_pred (pow_pos hp.pos 2)]
      push_cast
      ring
    refine Int.natCast_dvd_natCast.mp (by rw [hcast]; exact_mod_cast hD2)
  else
    have hcop : Nat.Coprime (l ^ k) m := Nat.Coprime.pow_left k (hl.coprime_iff_not_dvd.mpr hlm)
    refine (hcop.dvd_of_dvd_mul_right hlk).trans h24
private lemma helper_main (p m : ℕ) (hp : p.Prime) (a1 tau : ℤ) (h1 : IsCoprime a1 (m : ℤ)) (hpm : ¬ p ∣ m) (hC1 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * tau) (hC2 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * (tau ^ 2 - (p : ℤ) ^ 11 * ((p : ℤ) + 1))) : m ∣ (p ^ 2 - 1) / 24 := by
  if hp2 : p = 2 then
    subst hp2
    apply dvd_zero m
  else if hp3 : p = 3 then
    subst hp3
    apply dvd_zero m
  else
    have h24 : 24 ∣ p ^ 2 - 1 := twentyFour_dvd_sq_sub_one p hp (hp.five_le_of_ne_two_of_ne_three hp2 hp3)
    rw [Nat.dvd_div_iff_mul_dvd h24]
    apply (Nat.dvd_iff_prime_pow_dvd_dvd (p ^ 2 - 1) (24 * m)).mpr fun l k hl hlk => prime_pow_dvd_sq_sub_one p m hp a1 tau h1 hpm hC1 hC2 h24 l k hl hlk
private lemma ModularCurve.dvd_sq_sub_one_div_of_isCoprime_of_not_dvd (p m : ℕ) (hp : p.Prime) (a1 tau : ℤ) (h1 : IsCoprime a1 (m : ℤ)) (hpm : ¬ p ∣ m) (hC1 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * tau) (hC2 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * (tau ^ 2 - (p : ℤ) ^ 11 * ((p : ℤ) + 1))) : m ∣ (p ^ 2 - 1) / 24 := helper_main p m hp a1 tau h1 hpm hC1 hC2
/--
[ModularCurve_dvd_sq_sub_one_div_of_isCoprime_of_not_dvd](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_dvd_sq_sub_one_div_of_isCoprime_of_not_dvd.lean)
-/
@[path]
private lemma main
  (p m : ℕ) (hp : p.Prime) (a1 tau : ℤ) (h1 : IsCoprime a1 (m : ℤ)) (hpm : ¬ p ∣ m)
  (hC1 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * tau)
  (hC2 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * (tau ^ 2 - (p : ℤ) ^ 11 * ((p : ℤ) + 1))) :
  -- imply
  m ∣ (p ^ 2 - 1) / 24 := ModularCurve.dvd_sq_sub_one_div_of_isCoprime_of_not_dvd p m hp a1 tau h1 hpm hC1 hC2


-- created on 2026-10-20
