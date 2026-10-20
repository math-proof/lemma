import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.QRDowlingQStirlingExpansion
open scoped BigOperators
open MetaMathlibExt


/--
[QRWhitney.whitneySecond_eq_sum_qStirlingSecond](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRDowlingQStirlingExpansion.lean)
-/
@[path]
private lemma QRWhitney_whitneySecond_eq_sum_qStirlingSecond_eq
  {m r q : ℂ}
  {qStirlingSecond : ℕ → ℕ → ℂ}
-- given
  (hq_zero_zero : qStirlingSecond 0 0 = 1)
  (hq_zero_succ : ∀ k : ℕ, qStirlingSecond 0 (k + 1) = 0)
  (hq_succ_zero : ∀ a : ℕ, qStirlingSecond (a + 1) 0 = 0)
  (hq_succ_succ : ∀ a k : ℕ, qStirlingSecond (a + 1) (k + 1) = q ^ k * qStirlingSecond a k + QRWhitney.qBrack q (k + 1) * qStirlingSecond a (k + 1)) :
-- imply
  ∀ a k : ℕ, QRWhitney.whitneySecond m r q a k =
    ∑ j ∈ Finset.range (a + 1),
    (Nat.choose a j : ℂ) * r ^ (a - j) * m ^ (j - k) *
    qStirlingSecond j k := by
-- proof
  apply MetaMathlibExt.QRWhitney.whitneySecond_eq_sum_qStirlingSecond m r q qStirlingSecond hq_zero_zero hq_zero_succ hq_succ_zero hq_succ_succ

/--
[eval_qrDowlingPolynomial_whitneySecond](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRDowlingQStirlingExpansion.lean)
-/
@[path]
private lemma eval_qrDowlingPolynomial_whitneySecond_eq
  {m r q x : ℂ}
  {n : ℕ}
  {qStirlingSecond : ℕ → ℕ → ℂ}
-- given
  (hq_zero_zero : qStirlingSecond 0 0 = 1)
  (hq_zero_succ : ∀ k : ℕ, qStirlingSecond 0 (k + 1) = 0)
  (hq_succ_zero : ∀ a : ℕ, qStirlingSecond (a + 1) 0 = 0)
  (hq_succ_succ : ∀ a k : ℕ, qStirlingSecond (a + 1) (k + 1) = q ^ k * qStirlingSecond a k + QRWhitney.qBrack q (k + 1) * qStirlingSecond a (k + 1)) :
-- imply
  Polynomial.eval x (qrDowlingPolynomial (QRWhitney.whitneySecond m r q) n) =
    ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℂ) * r ^ (n - k) *
    ∑ j ∈ Finset.range (k + 1),
    m ^ (k - j) * qStirlingSecond k j * x ^ j := by
-- proof
  apply MetaMathlibExt.eval_qrDowlingPolynomial_whitneySecond m r q x n qStirlingSecond hq_zero_zero hq_zero_succ hq_succ_zero hq_succ_succ

/--
[q_r_dowling_polynomial_q_stirling_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/QRDowlingQStirlingExpansion.lean)
-/
@[path]
private lemma q_r_dowling_polynomial_q_stirling_expansion_eq
  {q m r x : ℂ}
  {n : ℕ}
  {qStirlingSecond whitneySecond : ℕ → ℕ → ℂ}
  {dowlingPolynomial : ℕ → ℂ → ℂ}
-- given
  (hq_zero_zero : qStirlingSecond 0 0 = 1)
  (hq_zero_succ : ∀ k : ℕ, qStirlingSecond 0 (k + 1) = 0)
  (hq_succ_zero : ∀ a : ℕ, qStirlingSecond (a + 1) 0 = 0)
  (hq_succ_succ : ∀ a k : ℕ, qStirlingSecond (a + 1) (k + 1) = q ^ k * qStirlingSecond a k + (∑ i ∈ Finset.range (k + 1), q ^ i) * qStirlingSecond a (k + 1))
  (hW_zero_zero : whitneySecond 0 0 = 1)
  (hW_zero_succ : ∀ k : ℕ, whitneySecond 0 (k + 1) = 0)
  (hW_succ_zero : ∀ a : ℕ, whitneySecond (a + 1) 0 = r ^ (a + 1))
  (hW_succ_succ : ∀ a k : ℕ, whitneySecond (a + 1) (k + 1) = q ^ k * whitneySecond a k + (m * (∑ i ∈ Finset.range (k + 1), q ^ i) + r) * whitneySecond a (k + 1))
  (hD : ∀ a : ℕ, ∀ y : ℂ, dowlingPolynomial a y = ∑ k ∈ Finset.range (a + 1), whitneySecond a k * y ^ k) :
-- imply
  dowlingPolynomial n x =
    ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℂ) * r ^ (n - k) *
    ∑ j ∈ Finset.range (k + 1),
    m ^ (k - j) * qStirlingSecond k j * x ^ j := by
-- proof
  apply MetaMathlibExt.q_r_dowling_polynomial_q_stirling_expansion q m r x n qStirlingSecond whitneySecond dowlingPolynomial hq_zero_zero hq_zero_succ hq_succ_zero hq_succ_succ hW_zero_zero hW_zero_succ hW_succ_zero hW_succ_succ hD


-- created on 2026-10-20
