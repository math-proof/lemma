/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.QBinomialBasic.Part3
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

-- For qBinomialPoly 5 2: monotone functions Fin 2 → Fin 4
def h00 : Fin 2 → Fin 4 := ![0, 0]

def h01 : Fin 2 → Fin 4 := ![0, 1]

def h02 : Fin 2 → Fin 4 := ![0, 2]

def h03 : Fin 2 → Fin 4 := ![0, 3]

def h11 : Fin 2 → Fin 4 := ![1, 1]

def h12 : Fin 2 → Fin 4 := ![1, 2]

def h13 : Fin 2 → Fin 4 := ![1, 3]

def h22 : Fin 2 → Fin 4 := ![2, 2]

def h23 : Fin 2 → Fin 4 := ![2, 3]

def h33 : Fin 2 → Fin 4 := ![3, 3]

end Examples
end AlgebraicCombinatorics
