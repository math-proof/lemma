/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.WeightedSets.Part19
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

/-- Shifting by negative offset preserves shape structure -/
theorem Domino.shiftNeg_toShape (d : Domino) (offset : ℕ) :
    (d.shiftNeg offset).toShape = d.toShape.image (fun p => (p.1 - (offset : ℤ), p.2)) := by
  simp only [shiftNeg, shift_toShape]
  ext ⟨x, y⟩
  simp only [Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x', y'⟩, hp, hx, hy⟩
    exact ⟨⟨x', y'⟩, hp, by omega, hy⟩
  · rintro ⟨⟨x', y'⟩, hp, hx, hy⟩
    exact ⟨⟨x', y'⟩, hp, by omega, hy⟩

/-- Shifting by -k then by k returns the original domino -/
theorem Domino.shiftNat_shiftNeg (d : Domino) (k : ℕ) : (d.shiftNeg k).shiftNat k = d := by
  cases d <;> simp [shiftNat, shiftNeg, shift]

end DominoTilingsZ
end
