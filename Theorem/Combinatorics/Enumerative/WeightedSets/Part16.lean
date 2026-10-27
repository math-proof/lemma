/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.WeightedSets.Part21
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

/-- The left restriction at a fault is faultfree if k is the smallest fault -/
theorem restrictTilingLeft_isFaultfree (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) (hmin : ∀ j, j < k → ¬hasFault n T j) : 
    isFaultfree k (restrictTilingLeft n T k hk) := by
  constructor
  · exact hk.1
  · intro j hfault_restr
    -- We need to show False (i.e., no fault at j in the restricted tiling)
    -- A fault at j in the restricted tiling would imply a fault at j in T
    -- But j < k and hmin says there's no fault at j in T
    have hj_lt : j < k := hfault_restr.2.1
    have hj_lt_n : j < n := Nat.lt_trans hj_lt hk.2.1
    have hfault_T : hasFault n T j := by
      refine ⟨hfault_restr.1, hj_lt_n, ?_⟩
      intro d hd
      cases d with
      | horizontal i jj =>
        -- If d is in T.dominos, it's either in left part or right part
        have hlr := domino_left_or_right_at_fault hk (Domino.horizontal i jj) hd
        rcases hlr with hleft | hright
        · -- d is in left part, so it's in the restricted tiling
          have hd_restr : Domino.horizontal i jj ∈ (restrictTilingLeft n T k hk).dominos := by
            simp only [restrictTilingLeft, Set.mem_sep_iff]
            exact ⟨hd, hleft⟩
          exact hfault_restr.2.2 (Domino.horizontal i jj) hd_restr
        · -- d is in right part (x ≥ k+1), so i ≥ k+1 > j, hence i ≥ j+1
          simp only [Domino.inRightPart, Domino.toShape] at hright
          have hi := hright (i, jj) (by simp)
          have hj_lt_k : (j : ℤ) < k := by exact_mod_cast hj_lt
          right
          -- Need to show i ≥ j + 1
          -- We have hi : i ≥ k + 1 and hj_lt : j < k
          -- So i ≥ k + 1 > k > j, hence i ≥ j + 1
          omega
      | vertical _ _ => trivial
    exact hmin j hj_lt hfault_T

/-- The original dominos equal the union of left part and shifted right part -/
theorem dominos_eq_left_union_shifted_right (n : ℕ) (T : Tiling (Rectangle n 2)) (k : ℕ) 
    (hk : hasFault n T k) : 
    T.dominos = (restrictTilingLeft n T k hk).dominos ∪ 
                ((restrictTilingRight n T k hk).dominos.image (fun d => d.shiftNat k)) := by
  ext d
  simp only [Set.mem_union, Set.mem_image]
  simp only [restrictTilingLeft, restrictTilingRight, Set.mem_sep_iff, Set.mem_image]
  constructor
  · intro hd
    rcases domino_left_or_right_at_fault hk d hd with hleft | hright
    · left; exact ⟨hd, hleft⟩
    · right
      -- d is in right part, so d.shiftNeg k is in restrictTilingRight
      -- and (d.shiftNeg k).shiftNat k = d
      refine ⟨d.shiftNeg k, ⟨d, ⟨hd, hright⟩, rfl⟩, ?_⟩
      exact d.shiftNat_shiftNeg k
  · intro hd
    rcases hd with ⟨hd, _⟩ | ⟨d', ⟨d'', ⟨hd'', _⟩, hd'_eq⟩, hd_eq⟩
    · exact hd
    · -- d = d'.shiftNat k where d' = d''.shiftNeg k and d'' ∈ T.dominos
      subst hd'_eq hd_eq
      rw [Domino.shiftNat_shiftNeg]
      exact hd''

end DominoTilingsZ
end
