import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.ModularForm.HeckeOperator
open ModularForm


private lemma eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero' (k : ℤ) (N : ℕ) (a c : ℕ → ℂ) (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n) (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n) (h1 : a 1 = 0) : ∀ n : ℕ, n ≠ 0 → a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    if hlt : n < 2 then
      obtain rfl : n = 1 := by omega
      exact h1
    else
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      obtain ⟨m, rfl⟩ := hpn
      have hm0 : m ≠ 0 := by rintro rfl; simp at hn
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmlt : m < p * m := by nlinarith [hp.two_le]
      have ham : a m = 0 := ih m hmlt hm0
      if hpN : p ∣ N then
        have h := hU p hp hpN m
        rwa [ModularForm.coeffHeckeU_apply, ham, mul_zero, mul_comm m p] at h
      else
        have h := hT p hp hpN m
        rw [ModularForm.coeffHeckeT_apply, ham, mul_zero, mul_comm m p] at h
        if hpm : p ∣ m then
          obtain ⟨q, rfl⟩ := hpm
          have hq0 : q ≠ 0 := by rintro rfl; simp at hm0
          have hqlt : q < p * (p * q) := by
            have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
            nlinarith [hp.two_le]
          have haq : a q = 0 := ih q hqlt hq0
          rwa [if_pos (dvd_mul_right p q), Nat.mul_div_cancel_left q hp.pos, haq, mul_zero,
            add_zero] at h
        else
          rwa [if_neg hpm, add_zero] at h
private lemma coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one' (k : ℤ) (N : ℕ) (a c : ℕ → ℂ) (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n) (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n) (h1 : a 1 = 1) : ∀ p : ℕ, p.Prime → c p = a p := by
  intro p hp
  if hpN : p ∣ N then
    have h := hU p hp hpN 1
    rw [ModularForm.coeffHeckeU_apply, one_mul, h1, mul_one] at h
    apply h.symm
  else
    have h := hT p hp hpN 1
    rw [ModularForm.coeffHeckeT_apply, if_neg hp.not_dvd_one, add_zero, one_mul, h1, mul_one] at h
    apply h.symm
/--
[ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one.lean)
-/
@[path]
private lemma main
  {k : ℤ}
  {N : ℕ}
  {a c : ℕ → ℂ}
-- given
  (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
  (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
  (hone : a 1 = 1) :
-- imply
  ∀ p : ℕ, p.Prime → c p = a p :=
-- proof
  coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one' k N a c hT hU hone


-- created on 2026-10-23
