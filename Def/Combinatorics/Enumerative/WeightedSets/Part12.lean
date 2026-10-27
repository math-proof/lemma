/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.WeightedSets.Part6
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

/-- The faultfree tiling of the 1×2 rectangle as a Subtype element -/
def faultfreeTiling_1_2 : {T : Tiling (Rectangle 1 2) // isFaultfree 1 T} :=
  ⟨tiling_1_2, tiling_1_2_faultfree⟩

/-- The unique faultfree tiling of width 2: two horizontal dominos -/
def twoHorizontalDominos : Tiling (Rectangle 2 2) where
  dominos := {Domino.horizontal 1 1, Domino.horizontal 1 2}
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd1 hd2
    rcases hd1 with rfl | rfl <;> rcases hd2 with rfl | rfl
    · exact (hne rfl).elim
    · simp only [Set.disjoint_iff, Set.subset_empty_iff]; ext x
      simp only [Domino.toShape, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
                 Set.mem_empty_iff_false, iff_false, not_and]
      intro h1; rcases h1 with rfl | rfl <;> (intro h2; rcases h2 with h | h <;> simp_all)
    · simp only [Set.disjoint_iff, Set.subset_empty_iff]; ext x
      simp only [Domino.toShape, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
                 Set.mem_empty_iff_false, iff_false, not_and]
      intro h1; rcases h1 with rfl | rfl <;> (intro h2; rcases h2 with h | h <;> simp_all)
    · exact (hne rfl).elim
  cover := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop,
               Domino.toShape, Rectangle, Set.mem_ofPred_eq]
    constructor
    · intro ⟨d, hd, hp⟩
      rcases hd with rfl | rfl <;>
        (simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp; rcases hp with rfl | rfl <;> omega)
    · intro ⟨h1, h2, h3, h4⟩
      have hp1 : p.1 = 1 ∨ p.1 = 2 := by omega
      have hp2 : p.2 = 1 ∨ p.2 = 2 := by omega
      rcases hp2 with hp2' | hp2'
      · use Domino.horizontal 1 1, Or.inl rfl
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hp1 with hp1' | hp1' <;> [left; right] <;> ext <;> omega
      · use Domino.horizontal 1 2, Or.inr rfl
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hp1 with hp1' | hp1' <;> [left; right] <;> ext <;> omega

/-! #### Decomposition Lemma (lem.gf.weighted-set.domino.fd) -/
/-! #### Helper definitions for tiling composition/decomposition -/


/-- Shift a domino horizontally by an offset -/
def Domino.shift (d : Domino) (offset : ℤ) : Domino :=
  match d with
  | .horizontal i j => .horizontal (i + offset) j
  | .vertical i j => .vertical (i + offset) j

end DominoTilingsZ
end
