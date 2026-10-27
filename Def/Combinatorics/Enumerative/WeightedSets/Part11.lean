/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.WeightedSets.Part5
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

namespace DominoTilingsZ

/-- The unique tiling of the 1×2 rectangle (one vertical domino) -/
def tiling_1_2 : Tiling (Rectangle 1 2) where
  dominos := {Domino.vertical 1 1}
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_singleton_iff] at hd1 hd2
    subst hd1 hd2
    exact (hne rfl).elim
  cover := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, exists_eq_left,
               Domino.toShape, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl
      · exact ⟨le_refl 1, le_refl 1, le_refl 1, by norm_num⟩
      · exact ⟨le_refl 1, le_refl 1, by norm_num, le_refl 2⟩
    · intro ⟨h1, h2, h3, h4⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      have hp1 : p.1 = 1 := by omega
      have hp2 : p.2 = 1 ∨ p.2 = 2 := by omega
      rcases hp2 with hp2eq | hp2eq
      · left; ext <;> omega
      · right; ext <;> omega

end DominoTilingsZ
end
