/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Contributors. All rights reserved.
SPDX-License-Identifier: Apache-2.0

Inversions, length and Lehmer codes for permutations.

This file formalizes Section 1.3 (subsections on inversions and Lehmer codes) from

## Main definitions

* `Perm.inv` - the set of inversions of a permutation
* `Perm.invCount` - the number of inversions (length/Coxeter length)
* `Perm.nonInv` - the set of non-inversions (pairs where order is preserved)
* `Perm.lehmerEntry` - the Lehmer entry ℓ_i(σ) at position i
* `Perm.lehmerCode` - the Lehmer code of a permutation (as a function `Fin n → ℕ`)
* `Perm.Iic0` - the notation [m]_0 = {0, 1, ..., m} for integers
* `Perm.Iic0Nat` - the notation [m]_0 = {0, 1, ..., m} for natural numbers
* `lehmerCodeSet` - the set H_n of valid Lehmer codes
* `Perm.longestElement` - the longest element w₀ (reversal permutation)

## Main results

* `Perm.inv_one` - the identity has no inversions
* `Perm.invCount_one` - the identity has length 0
* `Perm.invCount_inv` - length is preserved under taking inverses
* `Perm.invCount_mul_le` - the triangle inequality for inversions
* `Perm.invCount_le_choose` - the length is at most n choose 2
* `Perm.invCount_eq_zero_iff` - length 0 iff identity
* `Perm.inv_longestElement` - the longest element has all pairs as inversions
* `Perm.invCount_longestElement` - the longest element has length n choose 2
* `Perm.invCount_longestElement_mul` - invCount (w₀ * σ) = card(nonInv σ)
* `Perm.invCount_longestElement_mul'` - invCount (w₀ * σ) = n choose 2 - invCount σ
* `Perm.invCount_eq_choose_iff` - length n choose 2 iff longest element
* `Perm.invCount_eq_sum_lehmerCode` - length equals sum of Lehmer code entries
* `Perm.lehmerCode_bijective` - the Lehmer code map is a bijection
* `card_lehmerCodeSet` - |H_n| = n!

## Design note: Namespace and duplication

This file uses the `AlgebraicCombinatorics.Perm` namespace for definitions like `inv`, `invCount`,
and `lehmerCode`. The file `Inversions2.lean` defines equivalent versions in the `Equiv.Perm`
namespace (`inversions`, `length`, `lehmerCode`) with bridge lemmas proving definitional equality:

* `Equiv.Perm.inversions_eq_inv` : `inversions σ = Perm.inv σ` (by `rfl`)
* `Equiv.Perm.length_eq_invCount` : `length σ = Perm.invCount σ` (by `rfl`)

**Which definitions to use:**
- Use `AlgebraicCombinatorics.Perm.inv`/`invCount` when working with basic inversion properties,
  Lehmer codes, and the longest element (this file)
- Use `Equiv.Perm.inversions`/`length` when working with reduced words, simple transpositions,
  and Coxeter-style arguments (Inversions2.lean)

The definitions are definitionally equal, so theorems from either file can be used interchangeably.

**Lehmer code representations:**
- `AlgebraicCombinatorics.Perm.lehmerCode : Equiv.Perm (Fin n) → (Fin n → ℕ)` (function)
- `Equiv.Perm.lehmerCode : Perm (Fin n) → List ℕ` (list, via `lehmerCode_toList`)

Both represent the same mathematical object; use whichever is more convenient for your application.

## References

-/

import Mathlib
set_option maxHeartbeats 400000

/-! ### Inversions and length -/


namespace AlgebraicCombinatorics

open Finset BigOperators

namespace Perm

variable {n : ℕ}

/--
An inversion of a permutation σ ∈ S_n is a pair (i, j) of elements of [n]
such that i < j and σ(i) > σ(j).

See Definition 1.3.1 (def.perm.invs) in the source.
-/
def inv (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.filter (fun p => p.1 < p.2 ∧ σ p.1 > σ p.2) Finset.univ

/--
The length (or Coxeter length) of a permutation σ is the number of inversions of σ.
This is denoted ℓ(σ) in the source.

See Definition 1.3.1 (def.perm.invs) part (b) in the source.
-/
def invCount (σ : Equiv.Perm (Fin n)) : ℕ :=
  (inv σ).card

/--
The longest element w₀ ∈ S_n is the permutation with OLN n(n-1)(n-2)...21,
i.e., the reversal permutation.

Note: This is equivalent to `Fin.revPerm` from Mathlib. See `longestElement_eq_revPerm`.
-/
def longestElement (n : ℕ) : Equiv.Perm (Fin n) :=
  ⟨fun i => ⟨n - 1 - i.val, by omega⟩,
   fun i => ⟨n - 1 - i.val, by omega⟩,
   fun i => by simp [Fin.ext_iff]; omega,
   fun i => by simp [Fin.ext_iff]; omega⟩

/-! ### Helper lemmas for symmetry of length distribution -/


/--
The non-inversions of a permutation σ: pairs (i, j) with i < j and σ i < σ j.

This is the complement of `inv σ` within the set of ordered pairs.
The non-inversions are exactly the pairs where σ preserves the order.
-/
def nonInv (σ : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.filter (fun p => p.1 < p.2 ∧ σ p.1 < σ p.2) Finset.univ

/-- The set of all pairs (i, j) with i < j -/
def orderedPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.filter (fun p => p.1 < p.2) Finset.univ

/-! ### Lehmer codes -/
/-! #### The notation [m]_0 for {0, 1, ..., m}

See Definition 1.3.5 (def.perm.lehmer1) part (b) in the source.
-/


/--
For each m ∈ ℤ, we let [m]_0 denote the set {0, 1, ..., m}.
This is an empty set when m < 0.

See Definition 1.3.5 (def.perm.lehmer1) part (b) in the source.
-/
def Iic0 (m : ℤ) : Set ℕ := {n : ℕ | (n : ℤ) ≤ m}

/-- [m]_0 for natural numbers is just {0, 1, ..., m} -/
def Iic0Nat (m : ℕ) : Set ℕ := Set.Iic m

end Perm

/-! #### Lehmer entry and Lehmer code definitions -/


namespace Perm

variable {n : ℕ}

/--
For σ ∈ S_n and i ∈ [n], we define ℓ_i(σ) as the number of j > i such that σ(i) > σ(j).
This counts how many elements to the right of position i are smaller than σ(i).

This is the canonical definition of Lehmer entry used throughout the project.
The equivalent formulation `i < j ∧ σ j < σ i` is provided by `lehmerEntry_eq_filter_lt`.

See Definition 1.3.5 (def.perm.lehmer1) part (a) in the source.
-/
def lehmerEntry (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  (Finset.filter (fun j : Fin n => i < j ∧ σ i > σ j) Finset.univ).card

/--
The Lehmer code of σ ∈ S_n is the n-tuple (ℓ_1(σ), ℓ_2(σ), ..., ℓ_n(σ)).

This is the canonical definition using a function type `Fin n → ℕ`.
For the list representation, use `lehmerCode_toList`.

See Definition 1.3.5 (def.perm.lehmer1) part (e) in the source.
-/
def lehmerCode (σ : Equiv.Perm (Fin n)) : Fin n → ℕ :=
  fun i => lehmerEntry σ i

/--
The Lehmer code as a list representation.
This converts the function representation `Fin n → ℕ` to a `List ℕ`.
-/
def lehmerCode_toList (σ : Equiv.Perm (Fin n)) : List ℕ :=
  (List.finRange n).map (lehmerCode σ)

end Perm

/-! ### The set of Lehmer codes -/


/--
The set H_n of valid Lehmer codes. An n-tuple (j_1, ..., j_n) is in H_n
if and only if j_i ≤ n - i - 1 for each i ∈ [n].

This is [n-1]_0 × [n-2]_0 × ... × [0]_0.

See Definition 1.3.5 (def.perm.lehmer1) part (c) in the source.
-/
def lehmerCodeSet (n : ℕ) : Set (Fin n → ℕ) :=
  {f | ∀ i : Fin n, f i ≤ n - 1 - i.val}

-- Helper: the set of "remaining" elements at position i (not yet used in positions < i)
def remainingSet {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun x => ∀ j : Fin n, j < i → σ j ≠ x)

-- Count elements smaller than x in the remaining set
def countSmallerInRemaining {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) (x : Fin n) : ℕ :=
  ((remainingSet σ i).filter (· < x)).card

/-! ### Lexicographic order -/


/--
Lexicographic order on n-tuples of integers.
We say (a_1, ..., a_n) <_lex (b_1, ..., b_n) if there exists k ∈ [n]
such that a_k ≠ b_k and the smallest such k satisfies a_k < b_k.

Note: This is essentially `Pi.Lex (· < ·) (· < ·)` from Mathlib, specialized to `Fin n → ℤ`.
We define it directly here to match the source presentation.

See Definition 1.3.8 (def.perm.lehmer.lex-ord) in the source.
-/
def lexLt {n : ℕ} (a b : Fin n → ℤ) : Prop :=
  ∃ k : Fin n, (∀ i : Fin n, i < k → a i = b i) ∧ a k < b k

/-! ### Generating function for length -/

/-- The Lehmer code finset: all functions f : Fin n → ℕ with f i < n - i. -/
def lehmerCodeFinset (n : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun i : Fin n => Finset.range (n - i.val))

/-- The image of the Lehmer code map. -/
def lehmerCodeImage (n : ℕ) : Finset (Fin n → ℕ) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).image Perm.lehmerCode

end AlgebraicCombinatorics
