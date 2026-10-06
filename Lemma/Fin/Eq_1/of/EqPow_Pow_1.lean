import Mathlib
import sympy.Basic


/--
[QuotientGroup_eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_QuotientGroup_eq_one_of_pow_char_pow_eq_one_pi_units_quotient_constRange.lean)
-/
@[main]
private lemma main
  {K : Type u} [Field K]
  {p : ℕ} [Fact p.Prime] [CharP K p]
  {n s : ℕ}
  {ξ : (Fin s → Kˣ) ⧸ (Pi.constMonoidHom (Fin s) Kˣ).range}
-- given
  (hξ : ξ ^ (p ^ n) = 1) :
-- imply
  ξ = 1 := by
-- proof
  induction ξ using QuotientGroup.induction_on with
  | H lam =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hξ
    rw [QuotientGroup.eq_one_iff]
    obtain ⟨c, hc⟩ := hξ
    rcases Nat.eq_zero_or_pos s with hs | hs
    · subst hs
      exact ⟨1, funext fun i => i.elim0⟩
    · obtain ⟨i₀⟩ : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
      refine ⟨lam i₀, funext fun i => ?_⟩

      have hi : (lam i) ^ (p ^ n) = c := by
        have := congrFun hc i; simpa using this.symm
      have hi₀ : (lam i₀) ^ (p ^ n) = c := by
        have := congrFun hc i₀; simpa using this.symm
      change lam i₀ = lam i
      apply Units.ext
      apply (iterateFrobenius_inj K p n)
      rw [iterateFrobenius_def, iterateFrobenius_def, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hi, hi₀]


-- created on 2026-10-05
