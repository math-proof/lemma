import Mathlib
import sympy.Basic


/--
[ZMod_natCard_dvd_of_forall_pow_eq_one_units_prime_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ZMod_natCard_dvd_of_forall_pow_eq_one_units_prime_pow.lean)
-/
@[path]
private lemma main
  {p : ℕ}
  {q : ℕ}
  {H : Subgroup (ZMod (p ^ (padicValNat p q + 1)))ˣ}
-- given
  (hp : p.Prime)
  (_hq : q ≠ 0)
  (hH : ∀ x ∈ H, x ^ q = 1) :
-- imply
  Nat.card H ∣ q := by
-- proof
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (p ^ (padicValNat p q + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hexp : Monoid.exponent H ∣ q :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun g => Subtype.ext (by
      have := hH g.1 g.2; simpa using this))
  by_cases hp2 : p = 2
  · subst hp2
    have hcardU : Nat.card (ZMod (2 ^ (padicValNat 2 q + 1)))ˣ = 2 ^ padicValNat 2 q := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos _)]
      simp
    refine (Subgroup.card_subgroup_dvd_card H).trans ?_
    rw [hcardU]
    exact pow_padicValNat_dvd
  · have : IsCyclic (ZMod (p ^ (padicValNat p q + 1)))ˣ :=
      ZMod.isCyclic_units_of_prime_pow p hp hp2 _
    have : IsCyclic H := Subgroup.isCyclic H
    rw [← IsCyclic.exponent_eq_card]
    exact hexp


-- created on 2026-10-05
