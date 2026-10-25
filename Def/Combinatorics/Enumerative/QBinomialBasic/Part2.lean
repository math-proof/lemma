/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.QBinomialBasic
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

section QBinomial

variable {R : Type*} [CommSemiring R]

/-- The equivalence between monotone functions and Sym -/
noncomputable def monotoneEquivSym (k m : ℕ) :
    { f : Fin k → Fin (m + 1) // Monotone f } ≃ Sym (Fin (m + 1)) k where
  toFun := fun ⟨f, _⟩ => monotoneToSym k m f
  invFun := fun s => ⟨symToMonotone k m s, symToMonotone_monotone k m s⟩
  left_inv := fun ⟨f, hf⟩ => by simp [monotone_sort_eq k m f hf]
  right_inv := fun s => sym_monotone_sort_eq k m s

/-! ### Recurrence Relations -/
/-! ### Transpose of monotone functions

The following helper definitions and lemmas establish a bijection between monotone
functions `Fin k → Fin (m + 1)` and `Fin m → Fin (k + 1)` via transposition.
This is used to prove the symmetry of q-binomial coefficients. -/


/-- The transpose of a monotone function f : Fin k → Fin (m + 1).
Given f, we define g : Fin m → Fin (k + 1) by g(j) = #{i : f(i) > m - 1 - j}.
This corresponds to the conjugate/transpose of the partition encoded by f. -/
def transposeMonotone (k m : ℕ) (f : Fin k → Fin (m + 1)) : Fin m → Fin (k + 1) :=
  fun j => ⟨Finset.univ.filter (fun i => (f i).val > m - 1 - j.val) |>.card, by
    have : (Finset.univ.filter (fun i : Fin k => (f i).val > m - 1 - j.val)).card ≤ Finset.card Finset.univ :=
      Finset.card_filter_le _ _
    simp only [Finset.card_fin] at this
    omega⟩

/-! ### Product Formulas -/

end QBinomial

/-! ## Counting Partitions -/


section PartitionCount

/-- Equivalence between monotone functions `Fin k → Fin (ℓ + 1)` and multisets
of size k over `Fin (ℓ + 1)`. A monotone function is converted to a multiset
by taking its values (with multiplicity), and a multiset is converted to a
monotone function by sorting and indexing. -/
def monotoneFunctionsEquivSym (k ℓ : ℕ) :
    {f : Fin k → Fin (ℓ + 1) // Monotone f} ≃ Sym (Fin (ℓ + 1)) k := by
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  case toFun =>
    intro ⟨f, _⟩
    exact ⟨Multiset.ofList (List.ofFn f), by simp⟩
  case invFun =>
    intro s
    let sorted := s.val.sort (· ≤ ·)
    have hlen : sorted.length = k := by simp [sorted, Multiset.length_sort]
    refine ⟨fun i => sorted.get (i.cast hlen.symm), ?_⟩
    intro i j hij
    apply List.Pairwise.rel_get_of_le (Multiset.pairwise_sort s.val (· ≤ ·))
    exact hij
  case left_inv =>
    intro ⟨f, hf⟩
    dsimp only
    ext i
    dsimp only
    rw [Fin.val_inj]
    have h : (Multiset.ofList (List.ofFn f)).sort (· ≤ ·) = List.ofFn f := by
      simp only [Multiset.coe_sort]
      apply List.mergeSort_eq_self
      exact List.pairwise_ofFn.mpr (fun i j hij => hf (le_of_lt hij))
    have hlen : ((Multiset.ofList (List.ofFn f)).sort (· ≤ ·)).length = k := by simp
    have eq1 : ((Multiset.ofList (List.ofFn f)).sort (· ≤ ·)).get (i.cast hlen.symm) =
               ((Multiset.ofList (List.ofFn f)).sort (· ≤ ·))[i.val] := by
      rfl
    rw [eq1]
    simp only [h]
    simp [List.getElem_ofFn]
  case right_inv =>
    intro s
    apply Sym.ext
    simp only [Sym.coe_mk]
    have hlen : (s.val.sort (· ≤ ·)).length = k := by simp [Multiset.length_sort]
    have h1 : List.ofFn (fun i : Fin k => (s.val.sort (· ≤ ·)).get (i.cast hlen.symm)) =
              s.val.sort (· ≤ ·) := by
      apply List.ext_get
      · simp
      · intro i hi1 hi2
        simp only [List.get_ofFn]
        rfl
    rw [h1]
    exact Multiset.sort_eq s.val (· ≤ ·)

end PartitionCount

/-! ## Examples -/


section Examples

/-! ### Helper definitions for explicit enumeration of monotone functions

For small values of n and k, we can enumerate all monotone functions explicitly
and compute the q-binomial polynomial by direct summation. -/


-- For qBinomialPoly 3 2: monotone functions Fin 2 → Fin 2
def f00 : Fin 2 → Fin 2 := ![0, 0]

def f01 : Fin 2 → Fin 2 := ![0, 1]

def f11 : Fin 2 → Fin 2 := ![1, 1]

end Examples
end AlgebraicCombinatorics
