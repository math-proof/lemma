/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.WeightedSets.Part24
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

/-- The width of composing the tail equals the total width minus the first component width -/
theorem composeTilings_tail_width (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).1 = 
    (composeTilings k ts).1 - (ts ⟨0, by omega⟩).1 := by
  simp only [composeTilings, faultfreeTilingsTail]
  -- Sum over tail = total sum - first element
  have hsplit : ∑ i : Fin k, (ts i).1 = (ts ⟨0, by omega⟩).1 + 
                ∑ i : Fin (k - 1), (ts ⟨i.val + 1, by omega⟩).1 := by
    induction k with
    | zero => omega
    | succ n ih =>
      cases n with
      | zero => omega
      | succ m =>
        rw [Fin.sum_univ_succ]
        rfl
  omega

/-- Dominos from component 0 are in the left part at position (ts 0).1 -/
theorem composeTilings_component0_inLeftPart (k : ℕ) (hk : k ≥ 1)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (d : Domino) (hd : d ∈ (ts ⟨0, hk⟩).2.val.dominos) :
    d.inLeftPart (ts ⟨0, hk⟩).1 := by
  intro p hp
  have hsub := domino_subset_rect (ts ⟨0, hk⟩).1 (ts ⟨0, hk⟩).2.val d hd
  have hp_rect := hsub hp
  simp only [Rectangle, Set.mem_ofPred_eq] at hp_rect
  exact hp_rect.2.1

/-- Dominos from component i >= 1 are in the right part at position (ts 0).1 -/
theorem composeTilings_componentPos_inRightPart (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) (hi : i.val ≥ 1) (d : Domino) (hd : d ∈ (ts i).2.val.dominos) :
    (d.shiftNat (partialWidthSum k ts i)).inRightPart (ts ⟨0, by omega⟩).1 := by
  intro p hp
  -- The shifted domino has x-coordinates >= partialWidthSum k ts i + 1
  -- Since i >= 1, partialWidthSum k ts i >= (ts 0).1
  have hpws_ge : partialWidthSum k ts i ≥ (ts ⟨0, by omega⟩).1 := by
    have h0 : (⟨0, by omega⟩ : Fin k) < i := by simp [Fin.lt_def]; omega
    have := partialWidthSum_add_le k ts ⟨0, by omega⟩ i h0
    omega
  -- The original domino d has x-coords in [1, (ts i).1]
  have hd_x := domino_subset_rect (ts i).1 (ts i).2.val d hd
  -- After shifting, x-coords are in [1 + pws, (ts i).1 + pws]
  rw [Domino.shiftNat_toShape, Set.mem_image] at hp
  obtain ⟨p', hp', hp_eq⟩ := hp
  rw [Prod.ext_iff] at hp_eq
  have hp'_rect := hd_x hp'
  simp only [Rectangle, Set.mem_ofPred_eq] at hp'_rect
  have hx' : p'.1 ≥ 1 := hp'_rect.1
  calc p.1 = p'.1 + partialWidthSum k ts i := by omega
    _ ≥ 1 + (ts ⟨0, by omega⟩).1 := by omega
    _ = (ts ⟨0, by omega⟩).1 + 1 := by ring

/-- The left restriction of a composed tiling at the first boundary has the same dominos 
    as the first component -/
theorem restrictTilingLeft_composeTilings_dominos (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) 
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    (restrictTilingLeft (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault).dominos = (ts ⟨0, by omega⟩).2.val.dominos := by
  ext d
  simp only [restrictTilingLeft, composeTilings, composeTilings_dominos,
             Set.mem_iUnion, composeTilings_component_dominos, Set.mem_image]
  constructor
  · -- If d is in the left restriction, it came from component 0
    intro ⟨⟨i, d', hd', hd_eq⟩, hleft⟩
    -- d = d'.shiftNat (partialWidthSum k ts i)
    subst hd_eq
    -- If i = 0, then partialWidthSum = 0 and d' is in (ts 0).2.val.dominos
    -- If i >= 1, then d is in right part, contradiction with hleft
    by_cases hi : i.val = 0
    · -- i = 0
      have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [hi_eq] at hd' ⊢
      have hpws : partialWidthSum k ts ⟨0, by omega⟩ = 0 := 
        partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
      rw [hpws, Domino.shiftNat_zero]
      exact hd'
    · -- i >= 1, contradiction
      exfalso
      have hi_pos : i.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
      have hright := composeTilings_componentPos_inRightPart k hk ts i hi_pos d' hd'
      -- d'.shiftNat ... is in right part, but hleft says it's in left part
      have hcontra := hleft
      simp only [Domino.inLeftPart] at hcontra
      simp only [Domino.inRightPart] at hright
      -- Get a point in d'.shiftNat ...
      have hne := Domino.toShape_nonempty (d'.shiftNat (partialWidthSum k ts i))
      obtain ⟨p, hp⟩ := hne
      have h1 := hcontra p hp
      have h2 := hright p hp
      omega
  · -- If d is in (ts 0).2.val.dominos, it's in the composed tiling and in left part
    intro hd
    constructor
    · -- d is in composeTilings_dominos
      refine ⟨⟨0, by omega⟩, d, hd, ?_⟩
      have hpws : partialWidthSum k ts ⟨0, by omega⟩ = 0 := 
        partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
      rw [hpws, Domino.shiftNat_zero]
    · -- d is in left part
      exact composeTilings_component0_inLeftPart k (by omega) ts d hd

/-- The left restriction of a composed tiling equals the first component's tiling.
    This follows from `restrictTilingLeft_composeTilings_dominos` via `Tiling.ext`. -/
theorem restrictTilingLeft_composeTilings_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    restrictTilingLeft (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault = (ts ⟨0, by omega⟩).2.val := by
  apply Tiling.ext
  exact restrictTilingLeft_composeTilings_dominos k hk ts hfault

/-- Dominos from component i shifted and then unshifted by k gives back the original -/
theorem composeTilings_componentPos_dominos_unshift (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (i : Fin k) (hi : i.val ≥ 1) (d : Domino) (hd : d ∈ (ts i).2.val.dominos) :
    (d.shiftNat (partialWidthSum k ts i)).shiftNeg (ts ⟨0, by omega⟩).1 = 
    d.shiftNat (partialWidthSum k ts i - (ts ⟨0, by omega⟩).1) := by
  -- partialWidthSum k ts i >= (ts 0).1 for i >= 1
  have hpws_ge : partialWidthSum k ts i ≥ (ts ⟨0, by omega⟩).1 := by
    have h0 : (⟨0, by omega⟩ : Fin k) < i := by simp [Fin.lt_def]; omega
    have := partialWidthSum_add_le k ts ⟨0, by omega⟩ i h0
    omega
  cases d with
  | horizontal x y =>
    simp only [Domino.shiftNat, Domino.shiftNeg, Domino.shift]
    congr 1
    omega
  | vertical x y =>
    simp only [Domino.shiftNat, Domino.shiftNeg, Domino.shift]
    congr 1
    omega

/-- The partial width sum for the tail equals the original minus (ts 0).1 -/
theorem partialWidthSum_tail (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (j : Fin (k - 1)) :
    partialWidthSum (k - 1) (faultfreeTilingsTail k (by omega) ts) j = 
    partialWidthSum k ts ⟨j.val + 1, by omega⟩ - (ts ⟨0, by omega⟩).1 := by
  simp only [partialWidthSum, faultfreeTilingsTail]
  -- LHS: ∑ i : Fin j.val, (ts ⟨i.val + 1, ...⟩).1
  -- RHS: ∑ i : Fin (j.val + 1), (ts ⟨i.val, ...⟩).1 - (ts ⟨0, ...⟩).1
  -- Use Fin.sum_univ_succ on RHS
  have hrhs : ∑ i : Fin (j.val + 1), (ts ⟨i.val, by omega⟩).1 = 
              (ts ⟨0, by omega⟩).1 + ∑ i : Fin j.val, (ts ⟨i.succ.val, by omega⟩).1 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero]
  conv_rhs => rw [hrhs]
  -- Now goal: ∑ i : Fin j.val, (ts ⟨i.val + 1, ...⟩).1 = 
  --           (ts ⟨0, ...⟩).1 + ∑ i : Fin j.val, (ts ⟨i.succ.val, ...⟩).1 - (ts ⟨0, ...⟩).1
  -- Note: i.succ.val = i.val + 1
  have heq : ∑ i : Fin j.val, (ts ⟨i.succ.val, by omega⟩).1 = 
             ∑ i : Fin j.val, (ts ⟨i.val + 1, by omega⟩).1 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_succ]
  rw [heq]
  omega

/-- The right restriction of a composed tiling at the first boundary has the same dominos 
    as the composition of the tail -/
theorem restrictTilingRight_composeTilings_dominos (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) 
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    (restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault).dominos = 
    (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2.dominos := by
  -- The proof shows that:
  -- 1. Dominos in right restriction come from components i >= 1
  -- 2. After unshifting by (ts 0).1, they match the tail composition
  ext d
  simp only [restrictTilingRight, Set.mem_image, composeTilings, 
             composeTilings_dominos, Set.mem_iUnion, composeTilings_component_dominos]
  constructor
  · -- Forward direction: d is in restrictTilingRight → d is in composeTilings of tail
    intro ⟨d', ⟨⟨i, d'', hd'', hd'_eq⟩, hright⟩, hd_eq⟩
    -- d' = d''.shiftNat (partialWidthSum k ts i) is in right part
    -- d = d'.shiftNeg w0 = (d''.shiftNat (pws k ts i)).shiftNeg w0
    subst hd'_eq hd_eq
    -- If i = 0, then d' would be in left part (contradiction)
    -- So i >= 1
    by_cases hi : i.val = 0
    · -- i = 0: contradiction
      exfalso
      have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [hi_eq] at hd'' hright
      have hpws : partialWidthSum k ts ⟨0, by omega⟩ = 0 := partialWidthSum_zero k ts ⟨0, by omega⟩ rfl
      rw [hpws, Domino.shiftNat_zero] at hright
      have hleft := composeTilings_component0_inLeftPart k (by omega : k ≥ 1) ts d'' hd''
      -- d'' is in left part but hright says it's in right part
      have hne := Domino.toShape_nonempty d''
      obtain ⟨p, hp⟩ := hne
      have h1 := hleft p hp
      have h2 := hright p hp
      omega
    · -- i >= 1: d comes from component i
      have hi_pos : i.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
      -- The index in the tail is i - 1
      -- Need to show d'' is in (faultfreeTilingsTail k _ ts ⟨i.val - 1, _⟩).2.val.dominos
      have hd''_tail : d'' ∈ (faultfreeTilingsTail k (by omega) ts ⟨i.val - 1, by omega⟩).2.val.dominos := by
        simp only [faultfreeTilingsTail]
        have hi_eq' : i.val - 1 + 1 = i.val := by omega
        have hfin_eq : (⟨i.val - 1 + 1, by omega⟩ : Fin k) = i := Fin.ext hi_eq'
        rw [hfin_eq]
        exact hd''
      refine ⟨⟨i.val - 1, by omega⟩, d'', hd''_tail, ?_⟩
      -- Need: (d''.shiftNat (pws k ts i)).shiftNeg w0 = d''.shiftNat (pws (k-1) (tail) (i-1))
      -- Use composeTilings_componentPos_dominos_unshift and partialWidthSum_tail
      have hunshift := composeTilings_componentPos_dominos_unshift k hk ts i hi_pos d'' hd''
      rw [hunshift]
      congr 1
      have htail := partialWidthSum_tail k hk ts ⟨i.val - 1, by omega⟩
      -- htail says: pws (k-1) (tail ts) ⟨i.val - 1, _⟩ = pws k ts ⟨i.val - 1 + 1, _⟩ - w0
      -- We need: pws k ts i - w0 = pws (k-1) (tail ts) ⟨i.val - 1, _⟩
      have hi_eq' : i.val - 1 + 1 = i.val := by omega
      have hfin_eq : (⟨i.val - 1 + 1, by omega⟩ : Fin k) = i := Fin.ext hi_eq'
      rw [htail, hfin_eq]
  · -- Backward direction: d is in composeTilings of tail → d is in restrictTilingRight
    intro ⟨j, d', hd', hd_eq⟩
    -- j : Fin (k - 1), d' is in (tail ts j).2.val.dominos
    -- d = d'.shiftNat (pws (k-1) (tail ts) j)
    subst hd_eq
    -- The original index is j + 1
    let i : Fin k := ⟨j.val + 1, by omega⟩
    -- d' is in (ts i).2.val.dominos (since tail ts j = ts (j+1))
    have hd'_ts : d' ∈ (ts i).2.val.dominos := by
      simp only [faultfreeTilingsTail] at hd'
      exact hd'
    -- The shifted domino in composeTilings is d'.shiftNat (pws k ts i)
    have hi_pos : i.val ≥ 1 := by simp only [i, Nat.add_one_le_iff, Nat.zero_lt_succ]
    -- Show that d'.shiftNat (pws k ts i) is in right part
    have hright := composeTilings_componentPos_inRightPart k hk ts i hi_pos d' hd'_ts
    -- The unshifted version
    have hunshift := composeTilings_componentPos_dominos_unshift k hk ts i hi_pos d' hd'_ts
    -- pws (k-1) (tail ts) j = pws k ts i - w0
    have htail := partialWidthSum_tail k hk ts j
    -- So d'.shiftNat (pws (k-1) (tail ts) j) = (d'.shiftNat (pws k ts i)).shiftNeg w0
    refine ⟨d'.shiftNat (partialWidthSum k ts i), ⟨⟨i, d', hd'_ts, rfl⟩, hright⟩, ?_⟩
    rw [hunshift, htail]

/-- The right restriction of a composed tiling has the same dominos as the composition of the tail.
    Note: The tilings have different types (different width parameters), so we state this 
    as a domino equality rather than a tiling equality. Use `Tiling.ext` with the width 
    equality `composeTilings_tail_width` to convert to tiling equality when needed. -/
theorem restrictTilingRight_composeTilings_dominos_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    (restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault).dominos = 
    (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2.dominos :=
  restrictTilingRight_composeTilings_dominos k hk ts hfault

/-- The right restriction of a composed tiling equals the composition of the tail.
    This combines the width equality `composeTilings_tail_width` with the domino equality
    `restrictTilingRight_composeTilings_dominos_eq` to give a full tiling equality.
    
    Note: The two tilings have the same type because:
    - restrictTilingRight has width (composeTilings k ts).1 - (ts 0).1
    - composeTilings (k-1) (tail ts) has width (composeTilings k ts).1 - (ts 0).1 (by composeTilings_tail_width) -/
theorem restrictTilingRight_composeTilings_eq (k : ℕ) (hk : k ≥ 2)
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'}))
    (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
    restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2 
      (ts ⟨0, by omega⟩).1 hfault = 
    (composeTilings_tail_width k hk ts) ▸ (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2 := by
  -- The dominos are equal by restrictTilingRight_composeTilings_dominos_eq
  have hdominos := restrictTilingRight_composeTilings_dominos_eq k hk ts hfault
  -- Apply Tiling.ext after casting
  apply Tiling.ext
  rw [hdominos]
  -- The cast doesn't change dominos
  rw [Tiling.subst_dominos]

end DominoTilingsZ
end
