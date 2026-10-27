import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt

/--
[prime_gap_factorial_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/PrimeGapFactorial.lean)
-/
@[path]
lemma prime_gap_factorial_general
  {n p r : ℕ}
-- given
  (hrmin : ∀ q : ℕ, q.Prime → n < q → r ≤ q)
  (hp : p.Prime)
  (hlo : Nat.factorial n + 1 < p)
  (hhi : p < Nat.factorial n + r ^ 2) :
-- imply
  (p - Nat.factorial n).Prime := by
-- proof
  have hNpos : 0 < Nat.factorial n := Nat.factorial_pos n
  have hNle : Nat.factorial n ≤ p := by omega
  have hd2 : 2 ≤ p - Nat.factorial n := by omega
  have hdpos : 0 < p - Nat.factorial n := by omega
  have hdp : p - Nat.factorial n + Nat.factorial n = p :=
    Nat.sub_add_cancel hNle
  have hdr2 : p - Nat.factorial n < r ^ 2 := by omega
  -- Key claim: every prime divisor of the difference is at least `r`.
  have key : ∀ m : ℕ, m.Prime → m ∣ (p - Nat.factorial n) → r ≤ m := by
    intro m hm hmd
    by_contra hlt
    have hlt' : m < r := Nat.lt_of_not_ge hlt
    have hmn : m ≤ n := by
      by_contra hcon
      have hcon' : n < m := Nat.lt_of_not_ge hcon
      have hle := hrmin m hm hcon'
      omega
    have hmN : m ∣ Nat.factorial n := hm.dvd_factorial.mpr hmn
    have hmp : m ∣ p := by
      rw [← hdp]
      exact Nat.dvd_add hmd hmN
    have hpm : p = m := (hp.dvd_iff_eq hm.ne_one).mp hmp
    have hmle : m ≤ p - Nat.factorial n := Nat.le_of_dvd hdpos hmd
    omega
  by_contra hcon
  have hmin : (p - Nat.factorial n).minFac.Prime :=
    Nat.minFac_prime (by omega)
  have hdvd : (p - Nat.factorial n).minFac ∣ (p - Nat.factorial n) :=
    Nat.minFac_dvd _
  have hrle : r ≤ (p - Nat.factorial n).minFac := key _ hmin hdvd
  have hsq : (p - Nat.factorial n).minFac ^ 2 ≤ p - Nat.factorial n :=
    Nat.minFac_sq_le_self hdpos hcon
  have hrr : r ^ 2 ≤ p - Nat.factorial n :=
    le_trans (Nat.pow_le_pow_left hrle 2) hsq
  omega
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[prime_gap_factorial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/PrimeGapFactorial.lean)
-/
@[path]
lemma prime_gap_factorial
  {n p r : ℕ}
-- given
  (hr : r.Prime)
  (hrn : n < r)
  (hrmin : ∀ q : ℕ, q.Prime → n < q → r ≤ q)
  (hp : p.Prime)
  (hlo : Nat.factorial n + 1 < p)
  (hhi : p < Nat.factorial n + r ^ 2) :
-- imply
  (p - Nat.factorial n).Prime := by
-- proof
  exact prime_gap_factorial_general n p r hrmin hp hlo hhi

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
