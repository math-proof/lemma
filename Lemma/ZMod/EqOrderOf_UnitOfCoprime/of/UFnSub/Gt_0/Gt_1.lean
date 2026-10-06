import Mathlib
import sympy.Basic

open Polynomial

/--
[orderOf_unitOfCoprime_pow_sub_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_orderOf_unitOfCoprime_pow_sub_one.lean)
-/
@[main]
private lemma main
  {Q n : ℕ}
-- given
  (hQ : 1 < Q)
  (hn : 0 < n)
  (h : Q.Coprime (Q ^ n - 1)) :
-- imply
  orderOf (ZMod.unitOfCoprime Q h) = n := by
-- proof
  have hpos : ∀ k : ℕ, 1 ≤ Q ^ k := fun k => Nat.one_le_pow _ _ (by omega)
  have hu : ∀ k : ℕ, ((ZMod.unitOfCoprime Q h ^ k : (ZMod (Q ^ n - 1))ˣ) : ZMod (Q ^ n - 1))
      = ((Q ^ k : ℕ) : ZMod (Q ^ n - 1)) := by
    intro k; rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Nat.cast_pow]
  have hcast : ∀ k : ℕ, (ZMod.unitOfCoprime Q h ^ k = 1 ↔ Q ^ k ≡ 1 [MOD Q ^ n - 1]) := by
    intro k
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one, ← hu, Units.val_eq_one]
  rw [orderOf_eq_iff hn]
  constructor
  · rw [hcast]
    exact ((Nat.modEq_iff_dvd' (hpos n)).2 dvd_rfl).symm
  · intro k hkn hk0 hk
    rw [hcast] at hk
    have hdvd : Q ^ n - 1 ∣ Q ^ k - 1 := (Nat.modEq_iff_dvd' (hpos k)).1 hk.symm
    have hlt : Q ^ k < Q ^ n := Nat.pow_lt_pow_right hQ hkn
    have hkpos : 0 < Q ^ k - 1 := by
      have : 1 < Q ^ k := Nat.one_lt_pow hk0.ne' hQ
      omega
    have := Nat.le_of_dvd hkpos hdvd
    omega


-- created on 2026-10-05
