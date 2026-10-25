/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Contributors. All rights reserved.
Authors: AlgebraicCombinatorics Contributors
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.QBinomialBasic.Part4
open Polynomial Finset BigOperators

/-!
# q-Binomial Formulas

This file formalizes the q-binomial formulas from the Algebraic Combinatorics text,
including:
- The first q-binomial theorem
- The second q-binomial theorem (Potter's binomial theorem)
- Counting subspaces of finite-dimensional vector spaces over finite fields
- Limits of q-binomial coefficients

## Main Definitions (in namespace `AlgebraicCombinatorics.QBinomialRec`)

* `qBinomial`: The q-binomial coefficient `[n choose k]_q`, defined via q-Pascal recurrence
* `qFactorial`: The q-factorial `[n]_q!`
* `qNat`: The q-analog of natural number `[n]_q`

**Namespace structure:** All definitions in this file are in the sub-namespace
`AlgebraicCombinatorics.QBinomialRec` to avoid conflicts with the canonical definitions
in `QBinomialBasic.lean`. The canonical definitions use the monotone function sum formula,
while this file uses the q-Pascal recurrence. Both are equivalent (see `qBinomial_eq_sum_monotone`).

To use definitions from this file:
- Use full path: `AlgebraicCombinatorics.QBinomialRec.qBinomial`
- Or open the namespace: `open AlgebraicCombinatorics.QBinomialRec`

## Main Results

* `qBinomial_eq_sum_monotone`: Equivalence to the monotone function sum definition
* `qBinomial_eq_sum_subsets`: Equivalence to the subset sum formula
* `qBinomial_first_theorem`: The first q-binomial theorem
* `qBinomial_second_theorem`: The second q-binomial theorem (Potter's binomial theorem)
* `qBinomial_subspace_count`: The q-binomial coefficient counts k-dimensional subspaces
* `qBinomial_limit`: The limit of q-binomial coefficients as n → ∞

## References

* Section on q-binomial formulas from Algebraic Combinatorics lecture notes
* See also `QBinomialBasic.lean` for the canonical definition and basic properties
-/


/-!
## Sub-namespace for Recursive q-Binomial Definitions

The definitions `qNat`, `qFactorial`, `qBinomial`, and related theorems in this file
use the q-Pascal recurrence, which is different from the monotone function sum
definition in `QBinomialBasic.lean`. To avoid namespace conflicts when both files
are imported together, these definitions are placed in the `QBinomialRec` sub-namespace.

The equivalence between the two definitions is proven in `qBinomial_eq_sum_monotone`.

To use these definitions, either:
1. Open the namespace: `open AlgebraicCombinatorics.QBinomialRec`
2. Use the full path: `AlgebraicCombinatorics.QBinomialRec.qBinomial`
-/

/-!
### Definition def.pars.qbinom.qint: q-integers and q-factorials

This section formalizes the q-analogs of integers and factorials from Definition 2.3.2.

**Part (a)**: The q-integer `[n]_q = q^0 + q^1 + ... + q^{n-1} ∈ ℤ[q]`

**Part (b)**: The q-factorial `[n]_q! = [1]_q · [2]_q · ... · [n]_q ∈ ℤ[q]`

**Part (c)**: For any element `a` of a ring `A`, `[n]_a` and `[n]_a!` denote the results
of substituting `a` for `q` in `[n]_q` and `[n]_q!`, respectively.

### Remark rmk.pars.qbinom.qint.frac

For any `n ∈ ℕ`:
- `[n]_q = (1 - q^n)/(1 - q)` (in ℤ⟦q⟧ or in the field of rational functions)
- `[n]_1 = n`
- `[n]_1! = n!`
-/


namespace AlgebraicCombinatorics

namespace QBinomialRec

section QAnalogs

variable {R : Type*} [CommRing R]

/-- Definition def.pars.qbinom.qint (a): The q-integer `[n]_q`.

    The q-analog of a natural number is defined as the sum:
    `[n]_q = q^0 + q^1 + q^2 + ... + q^{n-1}`

    This equals `(1 - q^n)/(1 - q)` in appropriate rings (see `qNat_eq_geom_sum`).
    When evaluated at `q = 1`, this equals `n` (see `qNat_at_one`). -/
noncomputable def qNat (q : R) (n : ℕ) : R :=
  ∑ i ∈ range n, q ^ i

/-- Definition def.pars.qbinom.qint (b): The q-factorial `[n]_q!`.

    The q-factorial is defined as the product:
    `[n]_q! = [1]_q · [2]_q · ... · [n]_q`

    When evaluated at `q = 1`, this equals `n!` (see `qFactorial_at_one`). -/
noncomputable def qFactorial (q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, qNat q (i + 1)

/-- The q-binomial coefficient (Gaussian binomial coefficient)
    `[n choose k]_q = [n]_q! / ([k]_q! · [n-k]_q!)`.

    This is defined as a polynomial in q with integer coefficients.
    It counts partitions that fit in a k × (n-k) box, weighted by q^|λ|.

    We use the recurrence relation (q-Pascal's identity):
    [n choose k]_q = [n-1 choose k-1]_q + q^k · [n-1 choose k]_q

    This avoids division and works over any commutative ring.

    This definition is equivalent to `AlgebraicCombinatorics.qBinomial` in `QBinomialBasic.lean`,
    which uses the monotone function sum definition. The equivalence is proven in
    `qBinomial_eq_sum_monotone`. The argument order here is `(q : R) (n k : ℕ)` vs
    `(n k : ℕ) (q : R)` in `QBinomialBasic.lean`. -/
noncomputable def qBinomial (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinomial q n k + q ^ (k + 1) * qBinomial q n (k + 1)

/-!
### Remark rmk.pars.qbinom.qint.frac: Properties of q-integers and q-factorials

The following lemmas formalize the key properties from Remark 2.3.3:
- The geometric series formula: `[n]_q = (1 - q^n)/(1 - q)`
- Evaluation at 1: `[n]_1 = n` and `[n]_1! = n!`
-/
/-!
### Proposition prop.pars.qbinom.alt-defs: Alternative definitions of q-binomial coefficients

This section formalizes the three equivalent characterizations of q-binomial coefficients
from Proposition 11.2.4 (prop.pars.qbinom.alt-defs) of the textbook.

**Part (a)**: Sum over weakly increasing tuples
  `[n choose k]_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ i_k ≤ n-k} q^{i₁ + i₂ + ... + i_k}`

**Part (b)**: Sum over k-element subsets
  `[n choose k]_q = ∑_{S ⊆ {1,...,n}, |S| = k} q^{sum(S) - (1 + 2 + ... + k)}`

**Part (c)**: Evaluation at q = 1 gives ordinary binomial coefficient
  `[n choose k]_1 = C(n, k)`

Part (c) is already proved as `qBinomial_at_one` above.
-/


-- Triangular number: 1 + 2 + ... + k
/-- The triangular number T(k) = 1 + 2 + ... + k = k(k+1)/2. -/
def triangular (k : ℕ) : ℕ := k * (k + 1) / 2

-- The set of monotone functions from Fin k to Fin (m + 1)
-- NOTE: We reuse the canonical definition from QBinomialBasic.lean.
-- The definition is copied here (not aliased) to maintain proof compatibility,
-- but it is definitionally equal to `AlgebraicCombinatorics.monotoneFunctions`.
/-- The set of monotone (weakly increasing) functions from Fin k to Fin (m + 1).
    This represents k-tuples (i₁, ..., i_k) with 0 ≤ i₁ ≤ i₂ ≤ ... ≤ i_k ≤ m.

    This is definitionally equal to `AlgebraicCombinatorics.monotoneFunctions`. -/
def monotoneFunctions (k m : ℕ) : Finset (Fin k → Fin (m + 1)) :=
  Finset.univ.filter fun f => Monotone f

/-- The sum of values of a function from Fin k to Fin (m + 1). -/
def sumValues (k m : ℕ) (f : Fin k → Fin (m + 1)) : ℕ :=
  ∑ i : Fin k, (f i).val

-- The set of k-element subsets of {1, 2, ..., n}
/-- The set of k-element subsets of {1, 2, ..., n}. -/
def kSubsetsOfIcc (n k : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter (fun S => S.card = k)

/-- The sum of elements in a finite set of natural numbers.

    Note: This is named `finsetSumNat` to distinguish from `AlgebraicCombinatorics.CauchyBinet.finsetSumFin`,
    which computes the sum of elements in a `Finset (Fin n)` by extracting their `.val`.
    Both compute "the sum of elements" but for different element types. -/
def finsetSumNat (S : Finset ℕ) : ℕ := S.sum id

/-- Proposition prop.pars.qbinom.alt-defs (a): Alternative definition of q-binomial as sum
    over weakly increasing tuples.

    [n choose k]_q = ∑_{0 ≤ i₁ ≤ i₂ ≤ ... ≤ i_k ≤ n-k} q^{i₁ + i₂ + ... + i_k}

    The sum ranges over all weakly increasing k-tuples (i₁, i₂, ..., i_k) with entries in {0, 1, ..., n-k}.
    When k = 0, this is a single term with exponent 0, giving 1.

    **Important**: This theorem requires `k ≤ n`. When k > n, the natural number subtraction
    `n - k = 0` in Lean, so `monotoneFunctions k 0` represents functions `Fin k → Fin 1`,
    which has exactly one element (the constant 0 function). This would give a sum of 1,
    but `qBinomial q n k = 0` when k > n (see `qBinomial_gt`).

    This characterization arises from the bijection between partitions fitting in a k × (n-k) box
    and weakly increasing k-tuples: a partition λ = (λ₁, ..., λ_k) with λ₁ ≤ n-k corresponds to
    the tuple (λ_k, λ_{k-1}, ..., λ₁) (reversed and possibly padded with zeros). -/

-- Helper definitions for the bijections in the proof of qBinomial_eq_sum_monotone
def monotoneFunctionsStartZero (k m : ℕ) : Finset (Fin (k + 1) → Fin (m + 1)) :=
  (monotoneFunctions (k + 1) m).filter fun f => f 0 = 0

def monotoneFunctionsStartPos (k m : ℕ) : Finset (Fin (k + 1) → Fin (m + 1)) :=
  (monotoneFunctions (k + 1) m).filter fun f => f 0 ≠ 0

def dropFirst (k m : ℕ) (f : Fin (k + 1) → Fin (m + 1)) : Fin k → Fin (m + 1) :=
  fun i => f i.succ

def prependZero (k m : ℕ) (g : Fin k → Fin (m + 1)) : Fin (k + 1) → Fin (m + 1) :=
  Fin.cons 0 g

def shiftDown (k m : ℕ) (f : Fin (k + 1) → Fin (m + 2)) (hf : ∀ i, (f i).val ≥ 1) :
    Fin (k + 1) → Fin (m + 1) :=
  fun i => ⟨(f i).val - 1, by have h1 := (f i).isLt; have h2 := hf i; omega⟩

def shiftUp (k m : ℕ) (g : Fin (k + 1) → Fin (m + 1)) : Fin (k + 1) → Fin (m + 2) :=
  fun i => ⟨(g i).val + 1, by have h := (g i).isLt; omega⟩

end QAnalogs

/-!
## Combinatorial Definition of q-Binomial Coefficients (Definition def.pars.qbinom.qbinom)

This section formalizes Definition 4.3.2 from the textbook, which defines the q-binomial
coefficient (Gaussian binomial coefficient) as a sum over partitions:

**(a)** The q-binomial coefficient `[n choose k]_q` is the polynomial
  `∑_{λ} q^|λ|`
where λ ranges over all partitions with largest part ≤ n-k and length ≤ k.

**(b)** For any ring element `a`, the evaluation `[n choose k]_a` is obtained by
substituting `a` for `q` in the polynomial `[n choose k]_q`.

### Key Properties

* When k > n, the q-binomial is 0 (empty sum since n - k < 0).
* `[n choose 0]_q = [n choose n]_q = 1` (only the empty partition qualifies).
* When a = 1, we recover the ordinary binomial coefficient: `[n choose k]_1 = C(n,k)`.
-/


section CombinatoricDefinition

/-- A partition has largest part ≤ m if all parts are ≤ m.
    This is used in the combinatorial definition of q-binomial coefficients. -/
def partitionLargestPartLeq {n : ℕ} (p : Nat.Partition n) (m : ℕ) : Prop :=
  ∀ i ∈ p.parts, i ≤ m

/-- A partition has length ≤ k if it has at most k parts.
    This is used in the combinatorial definition of q-binomial coefficients. -/
def partitionLengthLeq {n : ℕ} (p : Nat.Partition n) (k : ℕ) : Prop :=
  p.parts.card ≤ k

end CombinatoricDefinition
end QBinomialRec
end AlgebraicCombinatorics
