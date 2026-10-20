/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/PrimeGapFactorial.lean -/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial

namespace MetaMathlibExt

/-! # Prime gaps near n!
-/

/-- Prime gaps near `n!`, with only the hypotheses the argument uses: if every prime above `n`
is at least `r`, any prime `p` with `n! + 1 < p < n! + r^2` has `p - n!` prime as well.
`prime_gap_factorial` is the source-shaped form. -/
theorem prime_gap_factorial_general
    (n p r : ℕ) (hrmin : ∀ q : ℕ, q.Prime → n < q → r ≤ q)
    (hp : p.Prime) (hlo : Nat.factorial n + 1 < p)
    (hhi : p < Nat.factorial n + r ^ 2) :
    (p - Nat.factorial n).Prime := by
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
/--
Prime gaps near `n!`: with `r` the smallest prime above `n`, any prime `p`
with `n! + 1 < p < n! + r^2` has `p - n!` prime as well.

Source: Antonín Čejchan, Michal Křížek, and Lawrence Somer,
"On Remarkable Properties of Primes Near Factorials and Primorials,"
Journal of Integer Sequences 25 (2022), Article 22.1.4,
Theorem (label T1), lines 153–159,
https://cs.uwaterloo.ca/journals/JIS/VOL25/Krizek/krizek3.tex

The source's proof: a prime divisor `m` of the difference `p - n!` is
below `r`, hence at most `n`, so it divides `n!` and therefore `p`,
contradicting `p > n! + 1`. Verified computationally for `n = 0..8`.
It follows from `prime_gap_factorial_general`; the hypotheses `hr` and `hrn` are unused and
keep the source's shape.
Proves `Wanted` entry `prime_gap_factorial`.
-/
theorem prime_gap_factorial
    (n p r : ℕ)
    (hr : r.Prime) (hrn : n < r) (hrmin : ∀ q : ℕ, q.Prime → n < q → r ≤ q)
    (hp : p.Prime) (hlo : Nat.factorial n + 1 < p)
    (hhi : p < Nat.factorial n + r ^ 2) :
    (p - Nat.factorial n).Prime := by
  exact prime_gap_factorial_general n p r hrmin hp hlo hhi

end MetaMathlibExt
