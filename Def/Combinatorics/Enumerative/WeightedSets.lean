/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Structure.Combinatorics.Enumerative.WeightedSets
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

/-- A weighted set is finite-type if for each n ∈ ℕ, there are only finitely many
    elements of weight n. (Definition \ref{def.gf-ws.weighted-sets}(b)) -/
def IsFiniteType (W : WeightedSet α) : Prop :=
  ∀ n : ℕ, Set.Finite {a : α | W.weight a = n}

/-- The set of elements of a given weight in a weighted set -/
def elementsOfWeight (W : WeightedSet α) (n : ℕ) : Set α :=
  {a : α | W.weight a = n}

/-- For a finite-type weighted set, the count of elements of weight n -/
def countOfWeight (W : WeightedSet α) (hft : W.IsFiniteType) (n : ℕ) : ℕ :=
  (hft n).toFinset.card

/-! ### Weight Generating Function -/


/-- The weight generating function of a finite-type weighted set is the FPS
    ∑_{n ∈ ℕ} (# of elements of weight n) · x^n.
    (Definition \ref{def.gf-ws.weighted-sets}(c)) -/
def weightGenFun (W : WeightedSet α) (hft : W.IsFiniteType) : R⟦X⟧ :=
  PowerSeries.mk fun n => (W.countOfWeight hft n : R)

end WeightedSet
end
