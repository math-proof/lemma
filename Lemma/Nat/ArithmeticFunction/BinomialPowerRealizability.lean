import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.BinomialPowerRealizability
open MetaMathlibExt


/--
[doldRealizable_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/BinomialPowerRealizability.lean)
-/
@[path]
private lemma doldRealizable_dvd_eq
  {a : ℕ → ℤ}
  {n : ℕ}
-- given
  (h : doldRealizable a)
  (hn : 0 < n) :
-- imply
  (n : ℤ) ∣ ∑ d ∈ Nat.divisors n,
    (⇑ArithmeticFunction.moebius d) * a (n / d) := by
-- proof
  apply MetaMathlibExt.doldRealizable_dvd h n hn

/--
[doldRealizable_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/BinomialPowerRealizability.lean)
-/
@[path]
private lemma doldRealizable_nonneg_eq
  {a : ℕ → ℤ}
  {n : ℕ}
-- given
  (h : doldRealizable a)
  (hn : 0 < n) :
-- imply
  0 ≤ ∑ d ∈ Nat.divisors n,
    (⇑ArithmeticFunction.moebius d) * a (n / d) := by
-- proof
  apply MetaMathlibExt.doldRealizable_nonneg h n hn

/--
[doldRealizable_of_dvd_and_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/BinomialPowerRealizability.lean)
-/
@[path]
private lemma doldRealizable_of_dvd_and_nonneg_eq
  {a : ℕ → ℤ}
-- given
  (hdvd : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ ∑ d ∈ Nat.divisors n, (⇑ArithmeticFunction.moebius d) * a (n / d))
  (hnn : ∀ n : ℕ, 0 < n → 0 ≤ ∑ d ∈ Nat.divisors n, (⇑ArithmeticFunction.moebius d) * a (n / d)) :
-- imply
  doldRealizable a := by
-- proof
  apply MetaMathlibExt.doldRealizable_of_dvd_and_nonneg hdvd hnn

/--
[binomial_power_sequence_dold_realizable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/BinomialPowerRealizability.lean)
-/
@[path]
private lemma binomial_power_sequence_dold_realizable_eq
  :
-- imply
  ∀ r s : ℕ, 0 < r → doldRealizable
    (fun n => ((binomialPowerSeq r s n : ℕ) : ℤ)) := by
-- proof
  apply MetaMathlibExt.binomial_power_sequence_dold_realizable

/--
[binomialPowerSeq_dold_congruences](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/BinomialPowerRealizability.lean)
-/
@[path]
private lemma binomialPowerSeq_dold_congruences_eq
  {r s n : ℕ}
-- given
  (hr : 0 < r)
  (hn : 0 < n) :
-- imply
  (n : ℤ) ∣ ∑ d ∈ Nat.divisors n, (⇑ArithmeticFunction.moebius d) *
    ((binomialPowerSeq r s (n / d) : ℕ) : ℤ) := by
-- proof
  apply MetaMathlibExt.binomialPowerSeq_dold_congruences r s hr n hn

/--
[binomialPowerSeq_moebius_sum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/BinomialPowerRealizability.lean)
-/
@[path]
private lemma binomialPowerSeq_moebius_sum_nonneg_eq
  {r s n : ℕ}
-- given
  (hr : 0 < r)
  (hn : 0 < n) :
-- imply
  0 ≤ ∑ d ∈ Nat.divisors n, (⇑ArithmeticFunction.moebius d) *
    ((binomialPowerSeq r s (n / d) : ℕ) : ℤ) := by
-- proof
  apply MetaMathlibExt.binomialPowerSeq_moebius_sum_nonneg r s hr n hn


-- created on 2026-10-20
