/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.WeightedSets.Part13
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

/-- Shifting by 0 is the identity -/
@[simp]
theorem Domino.shift_zero (d : Domino) : d.shift 0 = d := by
  cases d <;> simp [shift]

/-- Shifting twice is the same as shifting by the sum -/
theorem Domino.shift_shift (d : Domino) (a b : ℤ) : (d.shift a).shift b = d.shift (a + b) := by
  cases d <;> simp [shift, add_assoc]

/-- Rectangle shift lemma -/
theorem Rectangle_shift (n m : ℕ) (offset : ℤ) :
    (Rectangle n m).image (fun p => (p.1 + offset, p.2)) = 
    {p : ℤ × ℤ | 1 + offset ≤ p.1 ∧ p.1 ≤ n + offset ∧ 1 ≤ p.2 ∧ p.2 ≤ m} := by
  ext ⟨x, y⟩
  simp only [Set.mem_image, Rectangle, Set.mem_ofPred_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x', y'⟩, ⟨h1, h2, h3, h4⟩, hx, hy⟩
    subst hx hy
    exact ⟨by omega, by omega, h3, h4⟩
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨(x - offset, y), ⟨by omega, by omega, h3, h4⟩, by omega, rfl⟩

end DominoTilingsZ
end
