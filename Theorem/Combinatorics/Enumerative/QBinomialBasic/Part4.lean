/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.QBinomialBasic.Part4
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

theorem monotoneFunctions_2_3_eq : monotoneFunctions 2 3 = {h00, h01, h02, h03, h11, h12, h13, h22, h23, h33} := by
  ext f
  simp only [monotoneFunctions, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro hf
    have h := hf (Fin.zero_le 1)
    match h0 : f 0, h1 : f 1 with
    | ⟨0, _⟩, ⟨0, _⟩ => left; ext i; fin_cases i <;> simp [h00, h0, h1]
    | ⟨0, _⟩, ⟨1, _⟩ => right; left; ext i; fin_cases i <;> simp [h01, h0, h1]
    | ⟨0, _⟩, ⟨2, _⟩ => right; right; left; ext i; fin_cases i <;> simp [h02, h0, h1]
    | ⟨0, _⟩, ⟨3, _⟩ => right; right; right; left; ext i; fin_cases i <;> simp [h03, h0, h1]
    | ⟨1, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨1, _⟩, ⟨1, _⟩ => right; right; right; right; left; ext i; fin_cases i <;> simp [h11, h0, h1]
    | ⟨1, _⟩, ⟨2, _⟩ => right; right; right; right; right; left; ext i; fin_cases i <;> simp [h12, h0, h1]
    | ⟨1, _⟩, ⟨3, _⟩ => right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [h13, h0, h1]
    | ⟨2, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨1, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨2, _⟩, ⟨2, _⟩ => right; right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [h22, h0, h1]
    | ⟨2, _⟩, ⟨3, _⟩ => right; right; right; right; right; right; right; right; left; ext i; fin_cases i <;> simp [h23, h0, h1]
    | ⟨3, _⟩, ⟨0, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨3, _⟩, ⟨1, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨3, _⟩, ⟨2, _⟩ => simp only [Fin.le_def] at h; rw [h0, h1] at h; simp at h
    | ⟨3, _⟩, ⟨3, _⟩ => right; right; right; right; right; right; right; right; right; ext i; fin_cases i <;> simp [h33, h0, h1]
  · intro hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals (intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [h00, h01, h02, h03, h11, h12, h13, h22, h23, h33])

theorem sum_h00 : ∑ i : Fin 2, (h00 i).val = 0 := by simp [h00]

theorem sum_h01 : ∑ i : Fin 2, (h01 i).val = 1 := by simp [h01]

theorem sum_h02 : ∑ i : Fin 2, (h02 i).val = 2 := by simp [h02]

theorem sum_h03 : ∑ i : Fin 2, (h03 i).val = 3 := by simp [h03]

theorem sum_h11 : ∑ i : Fin 2, (h11 i).val = 2 := by simp [h11]

theorem sum_h12 : ∑ i : Fin 2, (h12 i).val = 3 := by simp [h12]

theorem sum_h13 : ∑ i : Fin 2, (h13 i).val = 4 := by simp [h13]

theorem sum_h22 : ∑ i : Fin 2, (h22 i).val = 4 := by simp [h22]

theorem sum_h23 : ∑ i : Fin 2, (h23 i).val = 5 := by simp [h23]

theorem sum_h33 : ∑ i : Fin 2, (h33 i).val = 6 := by simp [h33]

/-- Example: `⟦3;2⟧_q = q^2 + q + 1`.

The partitions fitting in a 2 × 1 box are:
- (1, 1) with size 2
- (1) with size 1
- () with size 0 -/
example : qBinomialPoly 3 2 = X ^ 2 + X + 1 := by
  unfold qBinomialPoly
  have h1 : (2 : ℕ) ≤ 3 := by norm_num
  simp only [h1, ↓reduceIte]
  have h2 : (3 : ℕ) - 2 = 1 := by norm_num
  rw [h2, monotoneFunctions_2_1_eq]
  have hf00 : f00 ∉ ({f01, f11} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h <;> simp [f00, f01, f11] at h
  have hf01 : f01 ∉ ({f11} : Finset _) := by
    simp only [mem_singleton]
    intro h; simp [f01, f11] at h
  rw [sum_insert hf00, sum_insert hf01, sum_singleton]
  simp only [sum_f00, sum_f01, sum_f11]
  simp only [pow_zero, pow_one]
  ring

/-- Example: `⟦4;2⟧_q = q^4 + q^3 + 2q^2 + q + 1`.

The partitions fitting in a 2 × 2 box are:
- (2, 2) with size 4
- (2, 1) with size 3
- (2) with size 2
- (1, 1) with size 2
- (1) with size 1
- () with size 0 -/
example : qBinomialPoly 4 2 = X ^ 4 + X ^ 3 + 2 * X ^ 2 + X + 1 := by
  unfold qBinomialPoly
  have h1 : (2 : ℕ) ≤ 4 := by norm_num
  simp only [h1, ↓reduceIte]
  have h2 : (4 : ℕ) - 2 = 2 := by norm_num
  rw [h2, monotoneFunctions_2_2_eq]
  have hg00 : g00 ∉ ({g01, g02, g11, g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h <;> simp [g00, g01, g02, g11, g12, g22] at h
  have hg01 : g01 ∉ ({g02, g11, g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h <;> simp [g01, g02, g11, g12, g22] at h
  have hg02 : g02 ∉ ({g11, g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h <;> simp [g02, g11, g12, g22] at h
  have hg11 : g11 ∉ ({g12, g22} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h <;> simp [g11, g12, g22] at h
  have hg12 : g12 ∉ ({g22} : Finset _) := by
    simp only [mem_singleton]
    intro h; simp [g12, g22] at h
  rw [sum_insert hg00, sum_insert hg01, sum_insert hg02, sum_insert hg11, sum_insert hg12, sum_singleton]
  simp only [sum_g00, sum_g01, sum_g02, sum_g11, sum_g12, sum_g22]
  simp only [pow_zero, pow_one]
  ring

/-- Example: `⟦5;2⟧_q = 1 + q + 2q^2 + 2q^3 + 2q^4 + q^5 + q^6`.

Computed using Proposition 11.2.1(b). -/
example : qBinomialPoly 5 2 = 1 + X + 2 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 := by
  unfold qBinomialPoly
  have h1 : (2 : ℕ) ≤ 5 := by norm_num
  simp only [h1, ↓reduceIte]
  have h2 : (5 : ℕ) - 2 = 3 := by norm_num
  rw [h2, monotoneFunctions_2_3_eq]
  have hh00 : h00 ∉ ({h01, h02, h03, h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h | h | h | h <;> simp [h00, h01, h02, h03, h11, h12, h13, h22, h23, h33] at h
  have hh01 : h01 ∉ ({h02, h03, h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h | h | h <;> simp [h01, h02, h03, h11, h12, h13, h22, h23, h33] at h
  have hh02 : h02 ∉ ({h03, h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h | h <;> simp [h02, h03, h11, h12, h13, h22, h23, h33] at h
  have hh03 : h03 ∉ ({h11, h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h | h <;> simp [h03, h11, h12, h13, h22, h23, h33] at h
  have hh11 : h11 ∉ ({h12, h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h | h <;> simp [h11, h12, h13, h22, h23, h33] at h
  have hh12 : h12 ∉ ({h13, h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h | h <;> simp [h12, h13, h22, h23, h33] at h
  have hh13 : h13 ∉ ({h22, h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h | h <;> simp [h13, h22, h23, h33] at h
  have hh22 : h22 ∉ ({h23, h33} : Finset _) := by
    simp only [mem_insert, mem_singleton]
    intro h; rcases h with h | h <;> simp [h22, h23, h33] at h
  have hh23 : h23 ∉ ({h33} : Finset _) := by
    simp only [mem_singleton]
    intro h; simp [h23, h33] at h
  rw [sum_insert hh00, sum_insert hh01, sum_insert hh02, sum_insert hh03, sum_insert hh11, 
      sum_insert hh12, sum_insert hh13, sum_insert hh22, sum_insert hh23, sum_singleton]
  simp only [sum_h00, sum_h01, sum_h02, sum_h03, sum_h11, sum_h12, sum_h13, sum_h22, sum_h23, sum_h33]
  simp only [pow_zero, pow_one]
  ring

end Examples
end AlgebraicCombinatorics
