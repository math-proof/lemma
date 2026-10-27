/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.WeightedSets.Part18
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

/-- For k = 1, the composed dominos equal the original dominos (shifted by 0) -/
theorem composeTilings_dominos_one 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    composeTilings_dominos 1 ts = (ts 0).2.val.dominos := by
  simp only [composeTilings_dominos, composeTilings_component_dominos]
  -- Union over Fin 1 is just the single element
  ext d
  simp only [Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨i, d', hd', rfl⟩
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    have h0 : (0 : Fin 1).val = 0 := rfl
    simp only [partialWidthSum_zero 1 ts 0 h0, Domino.shiftNat_zero]
    exact hd'
  · intro hd
    refine ⟨0, d, hd, ?_⟩
    have h0 : (0 : Fin 1).val = 0 := rfl
    simp only [partialWidthSum_zero 1 ts 0 h0, Domino.shiftNat_zero]

/-- For k = 1, the composed tiling has the same dominos as the original -/
theorem composeTilings_one_dominos 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings 1 ts).2.dominos = (ts 0).2.val.dominos := by
  simp only [composeTilings]
  exact composeTilings_dominos_one ts

/-- For k = 1, the width of the composed tiling equals the width of the single component -/
theorem composeTilings_one_width 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings 1 ts).1 = (ts 0).1 := by
  simp only [composeTilings, Finset.univ_unique, Finset.sum_singleton]
  rfl

/-- For k = 1, the composed tiling equals the single component (as Tilings) -/
theorem composeTilings_one_tiling 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings 1 ts).2 = (ts 0).2.val := by
  apply Tiling.ext
  exact composeTilings_one_dominos ts

/-- For k = 1, the composed tiling is faultfree -/
theorem composeTilings_one_isFaultfree 
    (ts : Fin 1 → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    isFaultfree (composeTilings 1 ts).1 (composeTilings 1 ts).2 := by
  have h := (ts 0).2.property
  -- The width is (ts 0).1 and the tiling has the same dominos as (ts 0).2.val
  -- Since (ts 0).2.val is faultfree, so is the composed tiling
  constructor
  · -- Positive width
    have hpos : (ts 0).1 > 0 := h.1
    simp only [composeTilings, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
    exact hpos
  · -- No faults
    intro k hfault
    have hno_fault := h.2 k
    apply hno_fault
    rw [hasFault_eq_of_dominos_eq (composeTilings_one_dominos ts).symm]
    simp only [composeTilings] at hfault ⊢
    exact hfault

end DominoTilingsZ
end
