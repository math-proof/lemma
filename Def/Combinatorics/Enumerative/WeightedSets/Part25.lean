/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Theorem.Combinatorics.Enumerative.WeightedSets.Part20
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

/-- The decomposition function: given a tiling of a height-2 rectangle, produce a tuple
    of faultfree tilings by cutting along all faults.
    
    For example, a tiling with faults at positions k₁ < k₂ < ... < kₘ decomposes into
    m+1 faultfree tilings of widths k₁, k₂-k₁, ..., n-kₘ.
    
    The empty tiling (n=0) decomposes into the empty tuple (k=0). 
    
    Implementation: We recursively find the minimum fault position, cut the tiling there,
    and decompose the right part. The left part at a minimum fault is always faultfree.
    If no faults exist, the entire tiling is faultfree and returned as a singleton. -/
noncomputable def decomposeTiling : (n : ℕ) → (T : Tiling (Rectangle n 2)) → 
    Σ k : ℕ, Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})
  | 0, _ => ⟨0, Fin.elim0⟩
  | n + 1, T => 
    if hne : (faultPositions (n + 1) T).Nonempty then
      -- Has faults: cut at minimum fault
      let k := minFault (n + 1) T hne
      have hk : hasFault (n + 1) T k := minFault_hasFault (n + 1) T hne
      have hk_min : ∀ j, j < k → ¬hasFault (n + 1) T j := by
        intro j hj hfault
        have hle := minFault_le (n + 1) T hne j hfault
        omega
      let left := restrictTilingLeft (n + 1) T k hk
      let left_ff := restrictTilingLeft_isFaultfree (n + 1) T k hk hk_min
      let right := restrictTilingRight (n + 1) T k hk
      have hk_pos : k > 0 := hk.1
      have hk_lt : k < n + 1 := hk.2.1
      have hdec : n + 1 - k < n + 1 := by omega
      let ⟨m, ts⟩ := decomposeTiling (n + 1 - k) right
      ⟨m + 1, fun i => 
        if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ 
        else ts ⟨i.val - 1, by omega⟩⟩
    else
      -- No faults: T is faultfree
      have hff : isFaultfree (n + 1) T := by
        constructor
        · omega
        · intro k hfault
          exact hne ⟨k, hfault⟩
      ⟨1, fun _ => ⟨n + 1, ⟨T, hff⟩⟩⟩
termination_by n => n

end DominoTilingsZ
end
