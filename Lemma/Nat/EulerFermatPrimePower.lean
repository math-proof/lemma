import Mathlib
import Initialize.Tactic.Attr.Basic


namespace Nat

/--
[euler_fermat_prime_power_congruence_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerFermatPrimePower.lean)
-/
@[path]
lemma euler_fermat_prime_power_congruence_general
  {a p r : ℕ}
-- given
  (hp : Nat.Prime p)
  (hr : 1 ≤ r) :
-- imply
  Nat.ModEq (p ^ r) (a ^ (p ^ r)) (a ^ (p ^ (r - 1))) := by
-- proof
  have hp2 : 2 ≤ p := hp.two_le
  have haux : ∀ n : ℕ, n + 1 ≤ p ^ n := fun _ => Nat.lt_pow_self hp.one_lt
  by_cases hdiv : p ∣ a
  · -- Both sides divisible by p ^ r
    have hr0 : 0 < r := by omega
    have hle2 : r ≤ p ^ (r - 1) := by
      have h := haux (r - 1)
      have hrw : r - 1 + 1 = r := by omega
      omega
    have hle1 : r ≤ p ^ r := by
      calc r ≤ p ^ (r - 1) := hle2
        _ ≤ p ^ r := by
          apply Nat.pow_le_pow_right (by omega)
          omega
    have hdvd_pow1 : p ^ (p ^ r) ∣ a ^ (p ^ r) :=
      pow_dvd_pow_of_dvd hdiv (p ^ r)
    have hdvd_pow2 : p ^ (p ^ (r - 1)) ∣ a ^ (p ^ (r - 1)) :=
      pow_dvd_pow_of_dvd hdiv (p ^ (r - 1))
    have hdvd1 : p ^ r ∣ a ^ (p ^ r) := by
      apply dvd_trans _ hdvd_pow1
      apply Nat.pow_dvd_pow
      exact hle1
    have hdvd2 : p ^ r ∣ a ^ (p ^ (r - 1)) := by
      apply dvd_trans _ hdvd_pow2
      apply Nat.pow_dvd_pow
      exact hle2
    exact (hdvd1.modEq_zero_nat.trans hdvd2.modEq_zero_nat.symm)
  · -- Coprime case via Euler's theorem
    have hcop_p : p.Coprime a := (hp.coprime_iff_not_dvd).mpr hdiv
    have hcop : Nat.Coprime a (p ^ r) := hcop_p.symm.pow_right r
    have hr0 : 0 < r := by omega
    have htot : (p ^ r).totient = p ^ (r - 1) * (p - 1) :=
      Nat.totient_prime_pow hp hr0
    have hkey : a ^ ((p ^ r).totient) ≡ 1 [MOD p ^ r] :=
      Nat.ModEq.pow_totient hcop
    have hexp : p ^ r = p ^ (r - 1) + (p ^ r).totient := by
      rw [htot]
      conv_lhs => rw [show r = (r - 1) + 1 from by omega, pow_succ]
      have hpred : p = (p - 1) + 1 := by omega
      nth_rewrite 2 [hpred]
      ring
    conv_lhs => rw [hexp, pow_add]
    have hmul := (Nat.ModEq.refl (a ^ (p ^ (r - 1)))).mul hkey
    simpa using hmul
set_option linter.unusedVariables false in

end Nat

namespace Nat

/--
[euler_fermat_prime_power_congruence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerFermatPrimePower.lean)
-/
@[path]
lemma euler_fermat_prime_power_congruence
  {a p r : ℕ}
-- given
  (ha : 0 < a)
  (hp : Nat.Prime p)
  (hr : 1 ≤ r) :
-- imply
  Nat.ModEq (p ^ r) (a ^ (p ^ r)) (a ^ (p ^ (r - 1))) :=
-- proof
  euler_fermat_prime_power_congruence_general hp hr

end Nat


-- created on 2026-10-20
-- updated on 2026-10-26
