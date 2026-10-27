/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Notation.Combinatorics.Enumerative.WeightedSets.Part3
open PowerSeries Finset BigOperators

/-!
# The Generating Function of a Weighted Set

This file formalizes the theory of weighted sets and their weight generating functions,
following Section sec.gf.weighted-set of the Algebraic Combinatorics notes.

A weighted set is a set equipped with a weight function to ℕ. When the set is "finite-type"
(only finitely many elements of each weight), we can define its weight generating function
as a formal power series.

## Main Definitions

* `WeightedSet`: A set with a weight function to ℕ
* `WeightedSet.IsFiniteType`: Predicate for finite-type weighted sets
* `WeightedSet.weightGenFun`: The weight generating function of a finite-type weighted set
* `WeightedSet.Isomorphism`: Weight-preserving bijections between weighted sets
* `WeightedSet.disjointUnion`: Disjoint union of weighted sets (A + B)
* `WeightedSet.prod`: Product of weighted sets (A × B) with additive weights
* `WeightedSet.pow`: Cartesian power of a weighted set
* `WeightedSet.tuples`: Infinite disjoint union W^0 + W^1 + W^2 + ... (Kleene star)

## Main Results

* `WeightedSet.weightGenFun_eq_of_isomorphic`: Isomorphic weighted sets have equal generating functions
* `WeightedSet.weightGenFun_disjointUnion`: ḡ(A + B) = ḡ(A) + ḡ(B)
* `WeightedSet.weightGenFun_prod`: ḡ(A × B) = ḡ(A) · ḡ(B)
* `WeightedSet.weightGenFun_pow`: ḡ(A^k) = ḡ(A)^k
* `DominoTilingsZ.tiling_decomposition_isomorphism`: D ≅ F^0 + F^1 + F^2 + ... (Lemma lem.gf.weighted-set.domino.fd)

## Applications

The file includes applications to:
* Counting compositions (recovering the formula for the generating function of compositions)
* Domino tilings of height-2 rectangles (connection to Fibonacci numbers)

Note: Height-3 domino tilings are handled in `Details/DominoTilings.lean`.

## References

* [Flajolet and Sedgewick, *Analytic Combinatorics*, Part A][FlaSed09]
* [Fink, *Enumerative Combinatorics*, §3.3-§3.4][Fink17]

## Tags

weighted set, generating function, combinatorial class, domino tiling
-/


noncomputable section

variable {R : Type*} [CommSemiring R]

namespace WeightedSet

variable {α β γ : Type*}

/-! ### Cartesian Powers -/


/-- The k-th Cartesian power of a weighted set.
    Weight of (a₁, ..., aₖ) is |a₁| + ... + |aₖ|. -/
def pow (W : WeightedSet α) (k : ℕ) : WeightedSet (Fin k → α) where
  weight := fun f => ∑ i, W.weight (f i)

/-- Helper: pow (n+1) is isomorphic to W × pow n -/
def pow_succ_equiv (W : WeightedSet α) (n : ℕ) :
    Isomorphism (W.pow (n + 1)) (W ×ᵥ (W.pow n)) where
  toEquiv := (Fin.succFunEquiv α n).trans (Equiv.prodComm _ _)
  weight_eq := fun f => by
    simp only [pow, prod, Equiv.trans_apply, Equiv.prodComm_apply, Fin.succFunEquiv]
    rw [Fin.sum_univ_castSucc, add_comm]
    simp [Fin.last, Fin.natAdd, Fin.castSucc, Fin.castAdd]

/-! ### Infinite Disjoint Union (Tuples) -/


/-- The infinite disjoint union W^0 + W^1 + W^2 + ... of all tuples of elements.
    This is the "Kleene star" construction on weighted sets.
    An element is a pair (k, f) where k ∈ ℕ and f : Fin k → α is a k-tuple.
    The weight of (k, f) is the sum of weights of the entries: ∑ᵢ |f(i)|. -/
def tuples (W : WeightedSet α) : WeightedSet (Σ n : ℕ, Fin n → α) where
  weight := fun ⟨n, f⟩ => ∑ i : Fin n, W.weight (f i)

/-- A weighted set has positive weights if every element has weight ≥ 1 -/
def HasPositiveWeights (W : WeightedSet α) : Prop :=
  ∀ a : α, W.weight a ≥ 1

end WeightedSet

/-! ### Examples and Applications -/


namespace WeightedSetExamples

/-! #### Binary Strings (Example \ref{exa.ws.bin-string1}) -/


/-- Binary strings (finite tuples of 0s and 1s) with weight = length -/
def BinaryStrings : WeightedSet (List (Fin 2)) where
  weight := List.length

/-! #### Positive Integers -/


/-- The positive integers with weight = value -/
def PositiveIntegers : WeightedSet ℕ+ where
  weight := fun n => n.val

/-! #### Compositions -/


/-- Compositions of length k are k-tuples of positive integers -/
def Compositions (k : ℕ) : WeightedSet (Fin k → ℕ+) :=
  PositiveIntegers.pow k

end WeightedSetExamples
end
