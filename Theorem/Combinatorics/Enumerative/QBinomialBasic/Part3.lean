/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.QBinomialBasic.Part3
/-!
# q-Binomial Coefficients: Basic Definitions and Properties

This file introduces q-binomial coefficients (also known as Gaussian binomial coefficients)
and their basic properties. The q-binomial coefficient `⟦n;k⟧_q` is a polynomial in `q`
that serves as a q-analogue of the ordinary binomial coefficient.

**This file provides the canonical definition of q-binomial coefficients for this project.**

## Main Definitions

* `qInt`: The q-integer `[n]_q = 1 + q + q^2 + ... + q^(n-1)` (Definition 11.3.1)
* `qFactorial`: The q-factorial `[n]_q! = [1]_q * [2]_q * ... * [n]_q` (Definition 11.3.1)
* `qBinomial`: The q-binomial coefficient `⟦n;k⟧_q` (Definition 11.2.1) — **canonical definition**
* `qBinomialPoly`: The q-binomial coefficient as a polynomial in `ℤ[X]`
* `monotoneFunctions`: The set of monotone functions from `Fin k` to `Fin (m + 1)`

## Main Results

* `qBinomial_eq_sum_increasing_tuples`: Definition as sum over weakly increasing tuples
  (Proposition 11.2.1(a))
* `qBinomial_eq_partition_gf`: Equivalence to partition generating function
  (Definition 11.2.1(a))
* `qBinomial_eq_sum_subsets`: Alternative expression as sum over subsets (Proposition 11.2.1(b))
  -- Proved in `AlgebraicCombinatorics/Partitions/QBinomialFormulas.lean`
* `qBinomial_one_eq_binomial`: At q=1, we recover ordinary binomial coefficients
  (Proposition 11.2.1(c))
* `qBinomial_zero_of_lt`: q-binomial is zero when k > n (Proposition 11.2.2)
* `qBinomial_n_zero`: `⟦n;0⟧_q = 1` (Proposition 11.2.3)
* `qBinomial_n_n`: `⟦n;n⟧_q = 1` (Proposition 11.2.3)
* `qBinomial_rec_left`: Recurrence `⟦n;k⟧_q = q^(n-k) * ⟦n-1;k-1⟧_q + ⟦n-1;k⟧_q` (for 0 < k)
  (Theorem 11.2.4(a))
* `qBinomial_rec_right`: Recurrence `⟦n;k⟧_q = ⟦n-1;k-1⟧_q + q^k * ⟦n-1;k⟧_q` (for 0 < k)
  (Theorem 11.2.4(b))
* `qBinomial_quot_formula`: Product formula for q-binomial (Theorem thm.pars.qbinom.quot1(a))
* `qBinomial_eq_prod_quot`: Quotient formula for q-binomial (Theorem thm.pars.qbinom.quot1(b))
* `qInt_eq_geom_sum`: `[n]_q = (1 - q^n) / (1 - q)` (Remark 11.3.2)
* `qBinomial_eq_qFactorial_quot`: `⟦n;k⟧_q = [n]_q! / ([k]_q! * [n-k]_q!)` (Theorem 11.2.6)
* `qBinomial_symm`: Symmetry `⟦n;k⟧_q = ⟦n;n-k⟧_q` (Proposition 11.2.7)
* `card_partitions_with_parts_and_largest`: Counting partitions (Proposition 11.1.1)

## Implementation Notes

The q-binomial coefficient is defined via the sum over monotone tuples (Proposition 11.2.1(a)):
  `⟦n;k⟧_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ iₖ ≤ n-k} q^(i₁ + i₂ + ... + iₖ)`

This is equivalent to the generating function for partitions fitting in a k × (n-k) box
(Definition 11.2.1(a)), but the monotone tuple formulation is more directly computable
and avoids the need to sum over partitions of varying sizes.

We work over a general commutative semiring `R` with an element `q`, though the polynomial
version over `ℤ[q]` is the primary object of interest.

### Equivalent Formulations

The q-binomial coefficient has several equivalent definitions:

1. **Monotone function sum** (this definition): `∑_{f monotone} q^(∑ᵢ f(i))`
   See `qBinomial_eq_sum_increasing_tuples`.

2. **Subset sum formula**: `∑_{S ⊆ [n], |S|=k} q^(sum(S) - (1+2+...+k))`
   See `qBinomial_eq_sum_subsets` in `Partitions/QBinomialFormulas.lean`.

3. **q-Pascal recurrence**: `[n;k]_q = [n-1;k-1]_q + q^k · [n-1;k]_q`
   See `qBinomial_rec_right` (and `qBinomial_rec_left` for the dual form).

4. **q-factorial quotient**: `[n]_q! / ([k]_q! · [n-k]_q!)`
   See `qBinomial_eq_qFactorial_quot`.

Note: The file `Partitions/QBinomialFormulas.lean` defines equivalent versions of `qBinomial`
using the q-Pascal recurrence in the sub-namespace `AlgebraicCombinatorics.QBinomialRec`.
The file `SignedCounting/AlternatingSums.lean` defines a local version as `Polynomial ℤ`
in the namespace `AlgebraicCombinatorics.SignedCounting`. Both are proven equivalent to
this canonical definition via the theorems listed above.

## References

* Darij Grinberg, *Algebraic Combinatorics*, Section 11.2-11.3
* [Kac-Cheung, *Quantum Calculus*, Chapters 5-7]
* [Stanley, *Enumerative Combinatorics Vol. 1*]

## Tags

q-binomial, Gaussian binomial coefficient, q-integer, q-factorial, partition
-/


/-! ## q-Integers and q-Factorials -/


namespace AlgebraicCombinatorics

open Finset Polynomial BigOperators Nat

section Examples

theorem monotoneFunctions_2_2_eq : monotoneFunctions 2 2 = {g00, g01, g02, g11, g12, g22} := by
  ext f
  simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro hf
    have h := hf (Fin.zero_le 1)
    match h0 : f 0, h1 : f 1 with
    | ⟨0, _⟩, ⟨0, _⟩ => left; ext i; fin_cases i <;> simp [g00, h0, h1]
    | ⟨0, _⟩, ⟨1, _⟩ => right; left; ext i; fin_cases i <;> simp [g01, h0, h1]
    | ⟨0, _⟩, ⟨2, _⟩ => right; right; left; ext i; fin_cases i <;> simp [g02, h0, h1]
    | ⟨1, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨1, _⟩, ⟨1, _⟩ => right; right; right; left; ext i; fin_cases i <;> simp [g11, h0, h1]
    | ⟨1, _⟩, ⟨2, _⟩ => right; right; right; right; left; ext i; fin_cases i <;> simp [g12, h0, h1]
    | ⟨2, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨1, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨2, _⟩ => right; right; right; right; right; ext i; fin_cases i <;> simp [g22, h0, h1]
  · intro hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [g00, g01, g02, g11, g12, g22])

theorem sum_g00 : ∑ i : Fin 2, (g00 i).val = 0 := by simp [g00]

theorem sum_g01 : ∑ i : Fin 2, (g01 i).val = 1 := by simp [g01]

theorem sum_g02 : ∑ i : Fin 2, (g02 i).val = 2 := by simp [g02]

theorem sum_g11 : ∑ i : Fin 2, (g11 i).val = 2 := by simp [g11]

theorem sum_g12 : ∑ i : Fin 2, (g12 i).val = 3 := by simp [g12]

theorem sum_g22 : ∑ i : Fin 2, (g22 i).val = 4 := by simp [g22]

end Examples
end AlgebraicCombinatorics
