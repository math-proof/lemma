import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularForm.HeckeOperator
open ModularForm


private lemma coeffHeckeU_comm (p q : ℕ) (a : ℕ → ℂ) :
  coeffHeckeU p (coeffHeckeU q a) = coeffHeckeU q (coeffHeckeU p a) := by
  funext n
  simp only [coeffHeckeU_apply, Nat.mul_right_comm]

private lemma coeffHeckeT_coeffHeckeU_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) :
  coeffHeckeT k p (coeffHeckeU q a) = coeffHeckeU q (coeffHeckeT k p a) := by
  funext n
  simp only [coeffHeckeT_apply, coeffHeckeU_apply]
  have hiff : p ∣ n * q ↔ p ∣ n := hpq.dvd_mul_right
  if hpn : p ∣ n then
    rw [ite_eq_left hpn, ite_eq_left (hiff.mpr hpn), Nat.mul_right_comm, Nat.div_mul_right_comm hpn]
  else
    rw [ite_eq_right hpn, ite_eq_right (fun h => hpn (hiff.mp h)), Nat.mul_right_comm]
private lemma coeffHeckeT_comm (k : ℤ) {p q : ℕ} (hpq : Nat.Coprime p q) (a : ℕ → ℂ) :
  coeffHeckeT k p (coeffHeckeT k q a) = coeffHeckeT k q (coeffHeckeT k p a) := by
  funext n
  simp only [coeffHeckeT_apply]
  have hq : q ∣ n * p ↔ q ∣ n := hpq.symm.dvd_mul_right
  have hp : p ∣ n * q ↔ p ∣ n := hpq.dvd_mul_right
  have hpq' : ∀ {m : ℕ}, p ∣ m → (q ∣ m / p ↔ p * q ∣ m) := fun h =>
    Nat.dvd_div_iff_mul_dvd h
  have hqp' : ∀ {m : ℕ}, q ∣ m → (p ∣ m / q ↔ q * p ∣ m) := fun h =>
    Nat.dvd_div_iff_mul_dvd h
  if hpn : p ∣ n then
    if hqn : q ∣ n then
      have hpqn : p * q ∣ n := hpq.mul_dvd_of_dvd_of_dvd hpn hqn
      rw [ite_eq_left (hq.mpr hqn), ite_eq_left hpn, ite_eq_left ((hpq' hpn).mpr hpqn), ite_eq_left (hp.mpr hpn),
        ite_eq_left hqn, ite_eq_left ((hqp' hqn).mpr (mul_comm p q ▸ hpqn)),
        Nat.mul_right_comm, Nat.div_mul_right_comm hqn, Nat.div_mul_right_comm hpn,
        Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm q p]
      ring
    else
      have h1 : ¬ q ∣ n / p := fun h => hqn (Nat.dvd_trans (Nat.dvd_mul_left q p) ((hpq' hpn).mp h))
      rw [ite_eq_right (fun h => hqn (hq.mp h)), ite_eq_left hpn, ite_eq_right h1, ite_eq_left (hp.mpr hpn), ite_eq_right hqn,
        Nat.mul_right_comm, Nat.div_mul_right_comm hpn]
      ring
  else
    if hqn : q ∣ n then
      have h1 : ¬ p ∣ n / q := fun h => hpn (Nat.dvd_trans (Nat.dvd_mul_left p q) ((hqp' hqn).mp h))
      rw [ite_eq_left (hq.mpr hqn), ite_eq_right hpn, ite_eq_right (fun h => hpn (hp.mp h)), ite_eq_left hqn, ite_eq_right h1,
        Nat.mul_right_comm, Nat.div_mul_right_comm hqn]
      ring
    else
      rw [ite_eq_right (fun h => hqn (hq.mp h)), ite_eq_right hpn, ite_eq_right (fun h => hpn (hp.mp h)), ite_eq_right hqn,
        Nat.mul_right_comm]
/--
[ModularForm_coeffHeckeT_coeffHeckeU_comm](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_coeffHeckeT_coeffHeckeU_comm.lean)
-/
@[path]
private lemma main
  {k : ℤ}
  {p q : ℕ}
  {a : ℕ → ℂ}
-- given
  (hpq : Nat.Coprime p q) :
-- imply
  ModularForm.coeffHeckeT k p (ModularForm.coeffHeckeU q a) = ModularForm.coeffHeckeU q (ModularForm.coeffHeckeT k p a) :=
-- proof
  coeffHeckeT_coeffHeckeU_comm k hpq a


-- created on 2026-10-23
