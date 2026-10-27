/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.WeightedSets.Part17
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

/-- X-coordinate bounds for a shifted domino from a component -/
theorem shifted_domino_x_in_range' {n : ℕ} {T : Tiling (Rectangle n 2)} {d : Domino}
    (hd : d ∈ T.dominos) (offset : ℕ) (p : ℤ × ℤ) (hp : p ∈ (d.shiftNat offset).toShape) :
    1 + (offset : ℤ) ≤ p.1 ∧ p.1 ≤ n + (offset : ℤ) := by
  rw [Domino.shiftNat_toShape] at hp
  obtain ⟨p', hp', rfl⟩ := hp
  have hsub := domino_subset_rect n T d hd hp'
  simp only [Rectangle, Set.mem_ofPred_eq] at hsub
  simp only
  constructor <;> linarith

/-- Helper lemma for finding which component a point belongs to based on its x-coordinate.
    Given k components with widths, finds the unique component containing position x. -/
theorem find_component_index (k : ℕ) (widths : Fin k → ℕ) (x : ℕ) (hx : x < ∑ i, widths i) :
    ∃ i : Fin k, (∑ j : Fin i.val, widths ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) ≤ x ∧ 
                 x < (∑ j : Fin i.val, widths ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) + widths i := by
  induction k with
  | zero => 
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hx
    omega
  | succ k ih =>
    by_cases h : x < ∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
    · have ih' := ih (fun i => widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) h
      obtain ⟨i, hi1, hi2⟩ := ih'
      exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi1, hi2⟩
    · push Not at h
      have hsum : ∑ i : Fin (k + 1), widths i = 
          (∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + widths ⟨k, Nat.lt_succ_self k⟩ := by
        rw [Fin.sum_univ_castSucc]
        rfl
      have hx' : x < (∑ i : Fin k, widths ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + widths ⟨k, Nat.lt_succ_self k⟩ := by
        calc x < ∑ i : Fin (k + 1), widths i := hx
          _ = _ := hsum
      exact ⟨⟨k, Nat.lt_succ_self k⟩, h, hx'⟩

/-- Key lemma: partial width sums are monotonic -/
theorem partialWidthSum_add_le (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i1 i2 : Fin k) (h : i1 < i2) :
    partialWidthSum k ts i1 + (ts i1).1 ≤ partialWidthSum k ts i2 := by
  simp only [partialWidthSum]
  have hi : i1.val < i2.val := h
  have hle : i1.val + 1 ≤ i2.val := hi
  have hk : i1.val + 1 < k := Nat.lt_of_le_of_lt hi i2.isLt
  have hinj : Function.Injective (Fin.castLE hle) := Fin.castLE_injective hle
  have step1 : (∑ j : Fin i1.val, (ts ⟨j.val, Nat.lt_trans j.isLt i1.isLt⟩).1) + (ts i1).1 = 
               ∑ j : Fin (i1.val + 1), (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1 := by
    have heq := Fin.sum_univ_castSucc (fun j : Fin (i1.val + 1) => (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1)
    simp only [Fin.last, Fin.val_mk, Fin.val_castSucc] at heq
    linarith [heq]
  calc (∑ j : Fin i1.val, (ts ⟨j.val, Nat.lt_trans j.isLt i1.isLt⟩).1) + (ts i1).1
      = ∑ j : Fin (i1.val + 1), (ts ⟨j.val, Nat.lt_trans j.isLt hk⟩).1 := step1
    _ = ∑ j : Fin (i1.val + 1), (ts ⟨(Fin.castLE hle j).val, Nat.lt_trans (Fin.castLE hle j).isLt i2.isLt⟩).1 := by
          apply Finset.sum_congr rfl; intro x _; simp [Fin.castLE]
    _ = ∑ j ∈ (Finset.univ : Finset (Fin (i1.val + 1))).map ⟨Fin.castLE hle, hinj⟩, 
          (ts ⟨j.val, Nat.lt_trans j.isLt i2.isLt⟩).1 := by
          rw [Finset.sum_map]; simp
    _ ≤ ∑ j : Fin i2.val, (ts ⟨j.val, Nat.lt_trans j.isLt i2.isLt⟩).1 := by
          apply Finset.sum_le_univ_sum_of_nonneg; intro _; exact Nat.zero_le _

/-- Helper: Dominos from different components have disjoint x-coordinate ranges -/
theorem composeTilings_component_dominos_disjoint (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i1 i2 : Fin k) (hi : i1 ≠ i2)
    (d1 : Domino) (hd1 : d1 ∈ composeTilings_component_dominos k ts i1)
    (d2 : Domino) (hd2 : d2 ∈ composeTilings_component_dominos k ts i2) :
    Disjoint d1.toShape d2.toShape := by
  -- Get the original dominos
  simp only [composeTilings_component_dominos, Set.mem_image] at hd1 hd2
  obtain ⟨d1', hd1', rfl⟩ := hd1
  obtain ⟨d2', hd2', rfl⟩ := hd2
  -- WLOG i1 < i2
  wlog h : i1 < i2 generalizing i1 i2 d1' d2' with H
  · have h' : i2 < i1 := (lt_or_gt_of_ne hi).resolve_left h
    exact (H i2 i1 (Ne.symm hi) d2' hd2' d1' hd1' h').symm
  -- Key: partialWidthSum i1 + (ts i1).1 ≤ partialWidthSum i2
  have key : partialWidthSum k ts i1 + (ts i1).1 ≤ partialWidthSum k ts i2 := 
    partialWidthSum_add_le k ts i1 i2 h
  -- Prove disjointness using x-coordinate separation
  rw [Set.disjoint_iff]
  intro p ⟨hp1, hp2⟩
  have hx1 := shifted_domino_x_in_range' hd1' (partialWidthSum k ts i1) p hp1
  have hx2 := shifted_domino_x_in_range' hd2' (partialWidthSum k ts i2) p hp2
  have h1 : p.1 ≤ (ts i1).1 + partialWidthSum k ts i1 := hx1.2
  have h2 : 1 + partialWidthSum k ts i2 ≤ p.1 := hx2.1
  have h3 : (ts i1).1 + partialWidthSum k ts i1 < 1 + partialWidthSum k ts i2 := by
    calc (ts i1).1 + partialWidthSum k ts i1 
        = partialWidthSum k ts i1 + (ts i1).1 := by ring
      _ ≤ partialWidthSum k ts i2 := key
      _ < 1 + partialWidthSum k ts i2 := by omega
  linarith

/-- For any point p in the rectangle of total width, there exists a component i such that
    partialWidthSum k ts i < p.1 ≤ partialWidthSum k ts i + (ts i).1 -/
theorem point_in_some_component (k : ℕ) (_hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (p : ℤ × ℤ) (hp : p ∈ Rectangle (∑ i : Fin k, (ts i).1) 2) :
    ∃ i : Fin k, (partialWidthSum k ts i : ℤ) < p.1 ∧ 
                  p.1 ≤ partialWidthSum k ts i + (ts i).1 := by
  simp only [Rectangle, Set.mem_ofPred_eq] at hp
  have hp1_pos : p.1 ≥ 1 := hp.1
  have hp1_le : p.1 ≤ ∑ i : Fin k, (ts i).1 := hp.2.1
  -- p.1 - 1 is in range [0, totalWidth - 1]
  have hp1_nat : (p.1 - 1).toNat < ∑ i : Fin k, (ts i).1 := by omega
  -- Find the component using find_component_index
  obtain ⟨i, hi_lo, hi_hi⟩ := find_component_index k (fun j => (ts j).1) (p.1 - 1).toNat hp1_nat
  refine ⟨i, ?_, ?_⟩
  · -- partialWidthSum k ts i < p.1
    simp only [partialWidthSum]
    have h : (∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1 : ℤ) ≤ (p.1 - 1).toNat := by
      exact_mod_cast hi_lo
    omega
  · -- p.1 ≤ partialWidthSum k ts i + (ts i).1
    simp only [partialWidthSum]
    have h : ((p.1 - 1).toNat : ℤ) < ∑ j : Fin i.val, (ts ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).1 + (ts i).1 := by
      exact_mod_cast hi_hi
    omega

end DominoTilingsZ
end
