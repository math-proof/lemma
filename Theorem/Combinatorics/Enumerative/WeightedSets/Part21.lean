/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Enumerative.WeightedSets.Part25
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

/-- Decomposing a tiling with faults at the minimum fault position.
    This characterizes the structure of decomposeTiling when faults exist. -/
theorem decomposeTiling_hasFault (n : ℕ) (T : Tiling (Rectangle (n + 1) 2))
    (hne : (faultPositions (n + 1) T).Nonempty) :
    let k := minFault (n + 1) T hne
    let hk := minFault_hasFault (n + 1) T hne
    let hk_min : ∀ j, j < k → ¬hasFault (n + 1) T j := fun j hj hfault => 
      absurd (minFault_le (n + 1) T hne j hfault) (not_le.mpr hj)
    let left := restrictTilingLeft (n + 1) T k hk
    let left_ff := restrictTilingLeft_isFaultfree (n + 1) T k hk hk_min
    let right := restrictTilingRight (n + 1) T k hk
    let ⟨m, ts⟩ := decomposeTiling (n + 1 - k) right
    decomposeTiling (n + 1) T = 
      ⟨m + 1, fun i => if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ 
                       else ts ⟨i.val - 1, by omega⟩⟩ := by
  simp only [decomposeTiling, dite_eq_left hne]

/-- Decomposition followed by composition gives back the original tiling -/
theorem composeTilings_decomposeTiling (n : ℕ) (T : Tiling (Rectangle n 2)) :
    let ⟨k, ts⟩ := decomposeTiling n T
    composeTilings k ts = ⟨n, T⟩ := by
  simp only
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      -- n = 0 case: decomposeTiling returns ⟨0, Fin.elim0⟩
      have hdec : decomposeTiling 0 T = ⟨0, Fin.elim0⟩ := by unfold decomposeTiling; rfl
      rw [hdec]
      have hdom : (composeTilings 0 Fin.elim0).2.dominos = T.dominos := by
        cases T with
        | mk dominos pairwise_disjoint cover =>
          have hT_empty : dominos = ∅ := by
            have heqR : Rectangle 0 2 = ∅ := Rectangle_zero_left 2
            have hcover' : ⋃ d ∈ dominos, d.toShape = ∅ := by rw [cover]; exact heqR
            by_contra hne
            have hne' : dominos.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
            obtain ⟨d, hd⟩ := hne'
            have hsub : d.toShape ⊆ ∅ := by
              calc d.toShape ⊆ ⋃ d' ∈ dominos, d'.toShape := Set.subset_biUnion_of_mem hd
                _ = ∅ := hcover'
            have hdne : d.toShape.Nonempty := Domino.toShape_nonempty d
            exact Set.not_nonempty_empty (hdne.mono hsub)
          simp only [composeTilings, hT_empty]
          ext x
          simp only [composeTilings_dominos, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
          intro ⟨i, _⟩
          exact i.elim0
      have hw : (composeTilings 0 Fin.elim0).1 = 0 := by
        simp only [composeTilings, Finset.univ_eq_empty, Finset.sum_empty]
      apply Sigma.ext hw
      exact (eqRec_heq (φ := fun n => Tiling (Rectangle n 2)) hw (composeTilings 0 Fin.elim0).2).symm.trans
        (heq_of_eq <| by
          apply Tiling.ext
          simpa [Tiling.subst_dominos hw] using hdom)
    | n' + 1 =>
      -- n = n' + 1 case
      -- decomposeTiling (n' + 1) T branches on whether faults exist
      -- Case split on whether faults exist
      by_cases hne : (faultPositions (n' + 1) T).Nonempty
      · -- Has faults: cut at minimum fault
        -- Get the minimum fault position and related data
        set k := minFault (n' + 1) T hne with hk_def
        have hk : hasFault (n' + 1) T k := minFault_hasFault (n' + 1) T hne
        have hk_min : ∀ j, j < k → ¬hasFault (n' + 1) T j := by
          intro j hj hfault
          have hle := minFault_le (n' + 1) T hne j hfault
          omega
        have hk_pos : k > 0 := hk.1
        have hk_lt : k < n' + 1 := hk.2.1
        have hdec : n' + 1 - k < n' + 1 := by omega
        
        -- Set up the left and right parts
        set left := restrictTilingLeft (n' + 1) T k hk with hleft_def
        set right := restrictTilingRight (n' + 1) T k hk with hright_def
        have left_ff := restrictTilingLeft_isFaultfree (n' + 1) T k hk hk_min
        
        -- Get the decomposition of the right part (keeping definitional equality)
        set dec_right := decomposeTiling (n' + 1 - k) right with hdec_right_def
        
        -- Apply induction hypothesis to the right part
        have ih_right := ih (n' + 1 - k) hdec right
        -- ih_right : composeTilings dec_right.1 dec_right.2 = ⟨n' + 1 - k, right⟩
        
        -- Rewrite using decomposeTiling_hasFault to get the concrete form
        have hdecomp := decomposeTiling_hasFault n' T hne
        simp only at hdecomp
        rw [hdecomp]
        
        -- The goal is now in terms of the concrete decomposition
        -- We need to show that composing gives back ⟨n' + 1, T⟩
        
        -- Key facts we'll use:
        -- 1. ih_right tells us composeTilings on the right part gives back right
        -- 2. dominos_eq_left_union_shifted_right tells us T.dominos = left ∪ shifted(right)
        
        -- The proof strategy is to show both components are equal
        -- For this, we use the fact that Sigma types are equal iff both components are equal
        
        -- Define abbreviations for clarity
        let m := (decomposeTiling (n' + 1 - k) right).1
        let ts_rest := (decomposeTiling (n' + 1 - k) right).2
        
        -- Show the width equality first
        have hwidth : (composeTilings (m + 1) (fun i => 
            if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ else ts_rest ⟨i.val - 1, by omega⟩)).1 = n' + 1 := by
          simp only [composeTilings]
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Fin.val_succ, ↓reduceDIte, Nat.add_sub_cancel]
          have hsum : ∑ x : Fin m,
              (if h : x.val + 1 = 0 then ⟨k, ⟨left, left_ff⟩⟩ else ts_rest ⟨x.val, by omega⟩).1
              = ∑ i : Fin m, (ts_rest i).1 := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [dite_eq_right (Nat.add_one_ne_zero x.val)]
          rw [hsum]
          have h := congrArg Sigma.fst ih_right
          simp only [composeTilings] at h
          rw [h]
          omega
        
        -- For the tiling part, we need to show the dominos are equal
        -- This requires showing that the union of shifted components equals T.dominos
        -- 
        -- The proof involves showing:
        -- 1. Component 0 (left) contributes left.dominos (shifted by 0)
        -- 2. Components 1..m contribute the shifted composition of ts_rest
        -- 3. By IH, composeTilings m ts_rest = right
        -- 4. By dominos_eq_left_union_shifted_right, T.dominos = left ∪ shifted(right)
        
        -- Define the function ts' for clarity
        let ts' : Fin (m + 1) → (Σ w : ℕ, {T' : Tiling (Rectangle w 2) // isFaultfree w T'}) := 
          fun i => if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩ else ts_rest ⟨i.val - 1, by omega⟩
        
        -- Show the dominos equality
        -- composeTilings_dominos (m + 1) ts' = T.dominos
        -- By dominos_eq_left_union_shifted_right:
        -- T.dominos = left.dominos ∪ right.dominos.image (shiftNat k)
        
        have hT_dominos := dominos_eq_left_union_shifted_right (n' + 1) T k hk
        
        -- Show that the composed dominos equal left ∪ shifted(right)
        have hdominos_eq : (composeTilings (m + 1) ts').2.dominos = T.dominos := by
          -- Step 1: composeTilings dominos = composeTilings_dominos
          simp only [composeTilings]
          
          -- Step 2: Split the union into component 0 and components 1..m
          have hsplit : composeTilings_dominos (m + 1) ts' = 
              composeTilings_component_dominos (m + 1) ts' 0 ∪ 
              ⋃ j : Fin m, composeTilings_component_dominos (m + 1) ts' j.succ := by
            ext d
            simp only [composeTilings_dominos, Set.mem_iUnion, Set.mem_union]
            constructor
            · intro ⟨i, hi⟩
              rcases i.eq_zero_or_eq_succ with rfl | ⟨j, rfl⟩
              · left; exact hi
              · right; exact ⟨j, hi⟩
            · intro h
              rcases h with h | ⟨j, hj⟩
              · exact ⟨0, h⟩
              · exact ⟨j.succ, hj⟩
          rw [hsplit]
          
          -- Step 3: Component 0 is left.dominos (since partialWidthSum = 0)
          have hcomp0 : composeTilings_component_dominos (m + 1) ts' 0 = left.dominos := by
            simp only [composeTilings_component_dominos]
            have hpws0 : partialWidthSum (m + 1) ts' 0 = 0 := 
              partialWidthSum_zero (m + 1) ts' 0 rfl
            rw [hpws0]
            simp only [Domino.shiftNat_zero, Set.image_id']
            -- ts' 0 = ⟨k, ⟨left, left_ff⟩⟩
            have hts'0 : ts' 0 = ⟨k, ⟨left, left_ff⟩⟩ := by
              simp only [ts', Fin.val_zero, ↓reduceDIte]
            rw [hts'0]
          rw [hcomp0]
          
          -- Step 4: Show components 1..m equal right.dominos.image (shiftNat k)
          -- First, show the relationship between ts' j.succ and ts_rest j
          have hts'_succ : ∀ j : Fin m, ts' j.succ = ts_rest j := by
            intro j
            simp only [ts']
            simp only [Fin.val_succ, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
            rfl
          
          -- Key: partialWidthSum (m+1) ts' j.succ = k + partialWidthSum m ts_rest j
          have hpws_succ : ∀ j : Fin m, 
              partialWidthSum (m + 1) ts' j.succ = k + partialWidthSum m ts_rest j := by
            intro j
            simp only [partialWidthSum]
            -- The sum over Fin j.succ.val needs to be rewritten
            -- j.succ.val = j.val + 1
            -- We need: ∑ i : Fin (j.val + 1), (ts' ⟨i, ...⟩).1 = k + ∑ i : Fin j.val, (ts_rest ⟨i, ...⟩).1
            
            -- Define a simpler function for the sum
            let f : Fin j.succ.val → ℕ := fun i => (ts' ⟨i.val, Nat.lt_trans i.isLt j.succ.isLt⟩).1
            let g : Fin j.val → ℕ := fun i => (ts_rest ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩).1
            
            -- j.succ.val = j.val + 1 ≥ 1, so Fin j.succ.val has a 0 element
            have hpos : j.succ.val > 0 := by simp only [Fin.val_succ]; omega
            let zero_idx : Fin j.succ.val := ⟨0, hpos⟩
            
            -- Show f zero_idx = k
            have hf0 : f zero_idx = k := by
              simp only [f, zero_idx, ts', ↓reduceDIte]
            
            -- Show f i.succ = g i for i : Fin j.val
            have hf_succ : ∀ i : Fin j.val, f i.succ = g i := by
              intro i
              simp only [f, g, ts']
              simp only [Fin.val_succ, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
            
            -- Now use Fin.sum_univ_succ on f
            have h_sum : ∑ i : Fin j.succ.val, f i = f zero_idx + ∑ i : Fin j.val, f i.succ := by
              have h := Fin.sum_univ_succ f
              convert h using 2
              exact congrArg f (Fin.ext rfl).symm
            
            calc ∑ i : Fin j.succ.val, (ts' ⟨i.val, Nat.lt_trans i.isLt j.succ.isLt⟩).1
                = ∑ i : Fin j.succ.val, f i := rfl
              _ = f zero_idx + ∑ i : Fin j.val, f i.succ := h_sum
              _ = k + ∑ i : Fin j.val, f i.succ := by rw [hf0]
              _ = k + ∑ i : Fin j.val, g i := by simp only [hf_succ]
              _ = k + ∑ i : Fin j.val, (ts_rest ⟨i.val, Nat.lt_trans i.isLt j.isLt⟩).1 := rfl
          
          -- Now show ⋃ j : Fin m, composeTilings_component_dominos (m+1) ts' j.succ
          --         = (composeTilings_dominos m ts_rest).image (shiftNat k)
          have hrest : ⋃ j : Fin m, composeTilings_component_dominos (m + 1) ts' j.succ = 
              (composeTilings_dominos m ts_rest).image (fun d => d.shiftNat k) := by
            ext d
            simp only [Set.mem_iUnion, composeTilings_component_dominos, Set.mem_image,
                       composeTilings_dominos]
            constructor
            · -- Forward: d is in component j.succ of ts'
              intro ⟨j, hj⟩
              obtain ⟨d', hd', hd_eq⟩ := hj
              use d'.shiftNat (partialWidthSum m ts_rest j)
              constructor
              · -- d'.shiftNat (partialWidthSum m ts_rest j) is in composeTilings_dominos m ts_rest
                refine ⟨j, d', ?_, rfl⟩
                rw [hts'_succ] at hd'
                exact hd'
              · -- d = (d'.shiftNat ...).shiftNat k
                rw [← hd_eq, hpws_succ, Nat.add_comm, Domino.shiftNat_shiftNat]
            · -- Backward: d is in (composeTilings_dominos m ts_rest).image (shiftNat k)
              intro ⟨d'', hd''_mem, hd_eq⟩
              obtain ⟨j, d', hd', hd''_eq⟩ := hd''_mem
              refine ⟨j, ?_⟩
              refine ⟨d', ?_, ?_⟩
              · rw [hts'_succ]; exact hd'
              · rw [← hd_eq, ← hd''_eq, hpws_succ, Nat.add_comm, Domino.shiftNat_shiftNat]
          rw [hrest]
          
          -- Step 5: Use IH to relate composeTilings_dominos m ts_rest to right.dominos
          have hih_dominos : (composeTilings m ts_rest).2.dominos = right.dominos := by
            have h := congrArg (fun σ => σ.2.dominos) ih_right
            exact h
          
          -- composeTilings_dominos m ts_rest = (composeTilings m ts_rest).2.dominos
          have hcomp_dominos : composeTilings_dominos m ts_rest = (composeTilings m ts_rest).2.dominos := by
            simp only [composeTilings]
          
          rw [hcomp_dominos, hih_dominos]
          
          -- Step 6: Apply dominos_eq_left_union_shifted_right
          exact hT_dominos.symm
        
        -- Now use the dominos equality to prove the full equality
        -- We need: composeTilings (m + 1) ts' = ⟨n' + 1, T⟩
        -- We have: hwidth for the first component
        -- We have: hdominos_eq for the second component
        
        -- Since the dominos are equal and the widths are equal, the tilings are equal
        -- The key is to use Sigma.ext_iff
        
        -- First, we need to show the tilings are equal after casting
        have htiling_eq : hwidth ▸ (composeTilings (m + 1) ts').2 = T := by
          apply Tiling.ext
          rw [Tiling.subst_dominos]
          exact hdominos_eq
        
        -- The goal uses raw decomposeTiling expressions instead of m and ts'
        -- We need to convert using the definitional equalities
        show composeTilings (m + 1) ts' = ⟨n' + 1, T⟩
        
        -- Use Sigma.ext_iff to construct the equality
        rw [Sigma.ext_iff]
        refine ⟨hwidth, ?_⟩
        -- Now need to show HEq (composeTilings (m + 1) ts').2 T
        -- We have: hwidth ▸ (composeTilings (m + 1) ts').2 = T
        -- Use eqRec_heq_iff_heq: (h ▸ a ≍ b) ↔ (a ≍ b)
        exact eqRec_heq_iff.mp (heq_of_eq htiling_eq)
      · -- No faults: T is faultfree
        have hff : isFaultfree (n' + 1) T := by
          constructor
          · omega
          · intro k hfault
            exact hne ⟨k, hfault⟩
        -- Show that decomposeTiling returns a singleton
        have hne' : ¬(faultPositions (n' + 1) T).Nonempty := hne
        have hdecomp : decomposeTiling (n' + 1) T = 
          ⟨1, fun _ => ⟨n' + 1, ⟨T, hff⟩⟩⟩ := by
          simp only [decomposeTiling, dite_eq_right hne']
        rw [hdecomp]
        
        -- composeTilings 1 ts = ⟨(ts 0).1, (ts 0).2.val⟩ = ⟨n' + 1, T⟩
        apply Sigma.ext (composeTilings_one_width (fun _ => ⟨n' + 1, ⟨T, hff⟩⟩))
        exact heq_of_eq (composeTilings_one_tiling (fun _ => ⟨n' + 1, ⟨T, hff⟩⟩))

/-- Decomposition is invariant under type cast (subst).
    This is key for handling dependent types in the inverse proofs. -/
theorem decomposeTiling_subst {n m : ℕ} (h : n = m) (T : Tiling (Rectangle n 2)) :
    decomposeTiling n T = decomposeTiling m (h ▸ T) := by
  subst h
  rfl

/-- Decomposition depends only on width and dominos.
    If two tilings have the same width and dominos, their decompositions are equal. -/
theorem decomposeTiling_eq_of_dominos_eq {n m : ℕ} (h : n = m) 
    (T1 : Tiling (Rectangle n 2)) (T2 : Tiling (Rectangle m 2))
    (hdom : T1.dominos = T2.dominos) :
    decomposeTiling n T1 = decomposeTiling m T2 := by
  subst h
  have hT_eq : T1 = T2 := Tiling.ext T1 T2 hdom
  rw [hT_eq]

/-- Helper lemma for proving equality of sigma types with Fin-indexed functions.
    This is used to prove decomposeTiling_composeTilings in the k ≥ 2 case. -/
theorem sigma_fin_fun_ext {α : Type*} (n m : ℕ) (h : n = m) 
    (f : Fin n → α) (g : Fin m → α)
    (hfg : ∀ i : Fin m, f ⟨i.val, by omega⟩ = g i) :
    (⟨n, f⟩ : Σ k, Fin k → α) = ⟨m, g⟩ := by
  apply Sigma.ext h
  simp only
  apply Function.hfunext (by simp only [h])
  intro i j hij
  have hi_eq : i.val = j.val := by
    have : HEq i j := hij
    cases h
    exact (Fin.heq_ext_iff rfl).mp this
  rw [heq_eq_eq]
  have hj_eq : (⟨i.val, by omega⟩ : Fin m) = j := Fin.ext hi_eq
  rw [← hj_eq]
  have hi_eq' : (⟨i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
  conv_lhs => rw [← hi_eq']
  exact hfg ⟨i.val, by omega⟩

/-- Composition followed by decomposition gives back the original tuple.
    
    This theorem proves that composing faultfree tilings and then decomposing 
    recovers the original tuple of tilings.
    
    The proof handles two cases:
    1. If k = 0 (empty tuple), the composed tiling is empty (width 0), and 
       decomposeTiling returns the empty tuple by definition.
    2. If k > 0, the composed tiling has positive width, and we need to show that
       the faults in the composed tiling occur exactly at the partial width sums,
       so decomposing at those faults recovers the original pieces. -/
theorem decomposeTiling_composeTilings (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    decomposeTiling (composeTilings k ts).1 (composeTilings k ts).2 = ⟨k, ts⟩ := by
  -- Use strong induction on k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
      -- k = 0: empty tuple, composed tiling has width 0
      have hw : (composeTilings 0 ts).1 = 0 := by
        simp only [composeTilings, Finset.univ_eq_empty, Finset.sum_empty]
      rw [decomposeTiling_subst hw]
      have hdec : decomposeTiling 0 (hw ▸ (composeTilings 0 ts).2) = ⟨0, Fin.elim0⟩ := by
        unfold decomposeTiling
        rfl
      rw [hdec]
      apply Sigma.ext
      · rfl
      · exact heq_of_eq (funext fun i => i.elim0)
    | 1 =>
      -- k = 1: single faultfree tiling
      -- The key insight: composeTilings 1 ts produces a Sigma pair where
      -- the width equals (ts 0).1 and the tiling equals (ts 0).2.val
      -- Since the original tiling is faultfree, decomposeTiling returns a singleton
      
      -- First, set up the key properties
      have hwidth : (composeTilings 1 ts).1 = (ts 0).1 := composeTilings_one_width ts
      have htiling : (composeTilings 1 ts).2 = (ts 0).2.val := composeTilings_one_tiling ts
      have hff : isFaultfree (composeTilings 1 ts).1 (composeTilings 1 ts).2 := 
        composeTilings_one_isFaultfree ts
      have hpos : (ts 0).1 > 0 := (ts 0).2.property.1
      
      -- The composed tiling equals ⟨(ts 0).1, (ts 0).2.val⟩
      have hpair : composeTilings 1 ts = ⟨(ts 0).1, (ts 0).2.val⟩ := by
        apply Sigma.ext hwidth
        exact heq_of_eq htiling
      
      -- Rewrite the goal using this equality
      rw [hpair]
      -- Goal: decomposeTiling (ts 0).1 (ts 0).2.val = ⟨1, ts⟩
      
      -- Destructure ts 0 to get the width and the faultfree tiling together
      -- This avoids the dependent type issue
      rcases hts0 : ts 0 with ⟨m, T, hT_ff⟩
      -- Now hts0 : ts 0 = ⟨m, ⟨T, hT_ff⟩⟩
      
      -- Update the goal and hypotheses using hts0
      simp only [hts0] at hpos ⊢
      -- Now hpos : m > 0
      -- Goal: decomposeTiling m T = ⟨1, ts⟩
      
      -- Since m > 0, we can write m = n + 1 for some n
      -- Use match to handle the pattern matching in decomposeTiling
      match m, T, hT_ff, hpos, hts0 with
      | n + 1, T, hT_ff, hpos, hts0 =>
        -- m = n + 1
        have hne : ¬(faultPositions (n + 1) T).Nonempty := 
          faultPositions_not_nonempty_of_isFaultfree (n + 1) T hT_ff
        
        simp only [decomposeTiling, dite_eq_right hne]
        
        -- Goal: ⟨1, fun _ => ⟨n + 1, ⟨T, _⟩⟩⟩ = ⟨1, ts⟩
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
        funext i
        simp only [Fin.fin_one_eq_zero]
        
        -- Show ⟨n + 1, ⟨T, _⟩⟩ = ts 0
        -- We have hts0 : ts 0 = ⟨n + 1, ⟨T, hT_ff⟩⟩
        rw [hts0]
        -- Goal is now definitionally equal
    | k' + 2 =>
      -- k = k' + 2 ≥ 2: multiple components
      -- The composed tiling has faults at the boundaries between components
      have hk_ge2 : k' + 2 ≥ 2 := by omega
      
      -- 1. There is a fault at position (ts 0).1 (the boundary after the first component)
      have hfault := composeTilings_hasFault_at_boundary (k' + 2) hk_ge2 ts
      
      -- The fault positions are nonempty
      have hne : (faultPositions (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2).Nonempty := 
        ⟨(ts ⟨0, by omega⟩).1, hfault⟩
      
      -- 2. The minimum fault is at (ts 0).1
      have hmin_eq := composeTilings_minFault_eq (k' + 2) hk_ge2 ts hne
      
      -- 3. Apply induction hypothesis to the tail
      have ih_tail := ih (k' + 1) (by omega) (faultfreeTilingsTail (k' + 2) (by omega) ts)
      
      -- 4. The width of the composed tiling is positive
      have hwidth_pos : (composeTilings (k' + 2) ts).1 > 0 := by
        have h0 : (ts ⟨0, by omega⟩).1 > 0 := (ts ⟨0, by omega⟩).2.property.1
        have hle : (ts ⟨0, by omega⟩).1 ≤ (composeTilings (k' + 2) ts).1 := by
          simp only [composeTilings]
          apply Finset.single_le_sum (s := Finset.univ) (f := fun i => (ts i).1)
            (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
        omega
      
      -- 5. Key equalities for the restrict operations
      have hleft_eq := restrictTilingLeft_composeTilings_eq (k' + 2) hk_ge2 ts hfault
      have hright_eq := restrictTilingRight_composeTilings_eq (k' + 2) hk_ge2 ts hfault
      
      -- 6. The width of the right restriction equals the tail composition width
      have hright_width := composeTilings_tail_width (k' + 2) hk_ge2 ts
      
      -- The width W = (composeTilings (k' + 2) ts).1 is positive, so W = (W - 1) + 1
      have hW_eq : (composeTilings (k' + 2) ts).1 = ((composeTilings (k' + 2) ts).1 - 1) + 1 := by omega
      
      -- Use decomposeTiling_subst to convert to the form (n + 1)
      rw [decomposeTiling_subst hW_eq]
      
      -- Now we can apply decomposeTiling_hasFault
      -- First, convert the nonemptiness proof
      have hne' : (faultPositions (((composeTilings (k' + 2) ts).1 - 1) + 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2)).Nonempty := by
        -- faultPositions only depends on dominos, which are preserved by subst
        simp only [faultPositions, Set.Nonempty, Set.mem_ofPred_eq]
        obtain ⟨k, hk⟩ := hne
        use k
        simp only [hasFault] at hk ⊢
        simp only [Tiling.subst_dominos]
        constructor
        · exact hk.1
        constructor
        · -- k < ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1
          have h := hk.2.1
          simp only [Nat.sub_add_cancel hwidth_pos] at h ⊢
          exact h
        · exact hk.2.2
      
      -- Apply the hasFault characterization
      rw [decomposeTiling_hasFault ((composeTilings (k' + 2) ts).1 - 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne']
      
      -- Now we need to show the equality of sigma types
      -- LHS: ⟨m + 1, fun i => if i.val = 0 then ⟨minF, left⟩ else ts_right (i-1)⟩
      -- RHS: ⟨k' + 2, ts⟩
      
      -- Key: minF = (ts 0).1
      have hminF_eq : minFault (((composeTilings (k' + 2) ts).1 - 1) + 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne' = (ts ⟨0, by omega⟩).1 := by
        -- The width ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1
        have hW_simp : ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1 := 
          Nat.sub_add_cancel hwidth_pos
        -- The two fault position sets are equal because:
        -- 1. The dominos are the same (subst preserves dominos)
        -- 2. The width bound is the same (by hW_simp)
        have hfp_eq : faultPositions (((composeTilings (k' + 2) ts).1 - 1) + 1) 
            (hW_eq ▸ (composeTilings (k' + 2) ts).2) = 
            faultPositions (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2 := by
          apply Set.ext
          intro j
          simp only [faultPositions, Set.mem_ofPred_eq, hasFault, Tiling.subst_dominos]
          constructor
          · intro ⟨h1, h2, h3⟩
            refine ⟨h1, ?_, h3⟩
            simp only [hW_simp] at h2
            exact h2
          · intro ⟨h1, h2, h3⟩
            refine ⟨h1, ?_, h3⟩
            simp only [hW_simp]
            exact h2
        -- Use the fact that the sets are equal to show the minFaults are equal
        have hfinite1 := faultPositions_finite (((composeTilings (k' + 2) ts).1 - 1) + 1) 
            (hW_eq ▸ (composeTilings (k' + 2) ts).2)
        have hfinite2 := faultPositions_finite (composeTilings (k' + 2) ts).1 
            (composeTilings (k' + 2) ts).2
        have htoFinset_eq : hfinite1.toFinset = hfinite2.toFinset := by
          ext x
          simp only [Set.Finite.mem_toFinset]
          rw [hfp_eq]
        -- minFault is defined as min' of the toFinset
        unfold minFault
        -- The min' of equal finsets is equal
        have hne1 : hfinite1.toFinset.Nonempty := by
          rw [Set.Finite.toFinset_nonempty]
          exact hne'
        have hne2 : hfinite2.toFinset.Nonempty := by
          rw [Set.Finite.toFinset_nonempty]
          exact hne
        calc hfinite1.toFinset.min' _ 
            = hfinite1.toFinset.min' hne1 := rfl
          _ = hfinite2.toFinset.min' hne2 := by simp only [htoFinset_eq]
          _ = minFault (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2 hne := rfl
          _ = (ts ⟨0, by omega⟩).1 := hmin_eq
      
      -- The proof for k >= 2 requires showing:
      -- 1. The count (m + 1) equals k' + 2
      -- 2. The 0th element equals ts 0
      -- 3. The remaining elements equal ts 1, ts 2, etc.
      
      -- Set up the width simplification
      have hW_simp : ((composeTilings (k' + 2) ts).1 - 1) + 1 = (composeTilings (k' + 2) ts).1 := 
        Nat.sub_add_cancel hwidth_pos
      
      -- The hasFault proof for the subst'd tiling, using the minFault
      have hminF' := minFault_hasFault (((composeTilings (k' + 2) ts).1 - 1) + 1) 
          (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne'
      
      -- Key simplification: minFault equals (ts 0).1
      -- So we can work with (ts 0).1 directly
      
      -- The right restriction at minFault has the same width as the tail composition
      have hright_width_eq : (((composeTilings (k' + 2) ts).1 - 1) + 1) - 
          (minFault (((composeTilings (k' + 2) ts).1 - 1) + 1) (hW_eq ▸ (composeTilings (k' + 2) ts).2) hne') = 
          (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1 := by
        rw [hminF_eq, hW_simp]
        have htail := composeTilings_tail_width (k' + 2) hk_ge2 ts
        -- htail : (composeTilings (k' + 2 - 1) (tail ts)).1 = (composeTilings (k' + 2) ts).1 - (ts 0).1
        -- We need: (composeTilings (k' + 2) ts).1 - (ts 0).1 = (composeTilings (k' + 1) (tail ts)).1
        -- Note: k' + 2 - 1 = k' + 1, so this is just htail.symm with the k simplification
        -- Use congrArg to handle the dependent type
        have hk_simp : k' + 2 - 1 = k' + 1 := by omega
        calc (composeTilings (k' + 2) ts).1 - (ts ⟨0, by omega⟩).1 
            = (composeTilings (k' + 2 - 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1 := htail.symm
          _ = (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1 := by
              congr 1

      -- The key insight: decomposeTiling of the right restriction equals ⟨k' + 1, tail ts⟩
      -- This follows from:
      -- 1. The right restriction equals the tail composition (after cast)
      -- 2. By ih_tail, decomposeTiling of tail composition = ⟨k' + 1, tail ts⟩
      
      -- The proof involves showing:
      -- - First component: (decomposeTiling ... right').fst + 1 = k' + 2
      --   This follows from hright_width_eq and ih_tail
      -- - Second component: the functions match
      --   For i=0: ⟨minF, left⟩ = ts 0 (by hminF_eq and hleft_eq)
      --   For i>0: ts_right(i-1) = ts i (by ih_tail and faultfreeTilingsTail definition)
      
      -- Key helper lemmas established above:
      -- - hfault: hasFault at position (ts 0).1
      -- - hne: faultPositions is nonempty
      -- - hmin_eq: minFault = (ts 0).1
      -- - ih_tail: decomposeTiling of tail composition = ⟨k' + 1, tail ts⟩
      -- - hleft_eq: left restriction = (ts 0).2.val
      -- - hright_eq: right restriction = tail composition (after cast)
      -- - hright_width_eq: width of right = width of tail composition
      
      -- Abbreviations for readability
      let n' := (composeTilings (k' + 2) ts).1 - 1
      let T' := hW_eq ▸ (composeTilings (k' + 2) ts).2
      let minF := minFault (n' + 1) T' hne'
      let hminF'' := minFault_hasFault (n' + 1) T' hne'
      let hminF_min : ∀ j, j < minF → ¬hasFault (n' + 1) T' j := fun j hj hfault => 
        absurd (minFault_le (n' + 1) T' hne' j hfault) (not_le.mpr hj)
      let left := restrictTilingLeft (n' + 1) T' minF hminF''
      let left_ff := restrictTilingLeft_isFaultfree (n' + 1) T' minF hminF'' hminF_min
      let right := restrictTilingRight (n' + 1) T' minF hminF''
      
      -- The decomposition of the right part
      let decomp_right := decomposeTiling (n' + 1 - minF) right
      
      -- Step 1: Show decomposeTiling of right equals decomposeTiling of tail composition
      -- First, we need the dominos equality
      have hright_dominos : right.dominos = 
          (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).2.dominos := by
        -- right = restrictTilingRight of the subst'd tiling
        -- The subst'd tiling has the same dominos as the original
        have hsubst_dom : T'.dominos = (composeTilings (k' + 2) ts).2.dominos := 
          Tiling.subst_dominos hW_eq (composeTilings (k' + 2) ts).2
        -- minF = (ts 0).1
        have hminF_eq' : minF = (ts ⟨0, by omega⟩).1 := hminF_eq
        -- restrictTilingRight of T' at minF has the same dominos as the original
        have hrest_dom : (restrictTilingRight (n' + 1) T' minF hminF'').dominos = 
            (restrictTilingRight (composeTilings (k' + 2) ts).1 (composeTilings (k' + 2) ts).2 
              (ts ⟨0, by omega⟩).1 hfault).dominos := by
          simp only [restrictTilingRight, hsubst_dom, hminF_eq']
        rw [hrest_dom]
        exact restrictTilingRight_composeTilings_dominos_eq (k' + 2) hk_ge2 ts hfault
      
      -- Use decomposeTiling_eq_of_dominos_eq
      have hdecomp_eq : decomp_right = 
          decomposeTiling (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).1
            (composeTilings (k' + 1) (faultfreeTilingsTail (k' + 2) (by omega) ts)).2 := by
        apply decomposeTiling_eq_of_dominos_eq hright_width_eq right
        exact hright_dominos
      
      -- By ih_tail, decomposeTiling of tail composition = ⟨k' + 1, tail ts⟩
      have hdecomp_tail : decomp_right = ⟨k' + 1, faultfreeTilingsTail (k' + 2) (by omega) ts⟩ := by
        rw [hdecomp_eq]
        exact ih_tail
      
      -- Step 2: First component equality
      have h_fst : decomp_right.1 + 1 = k' + 2 := by
        simp only [hdecomp_tail]
      
      -- Step 3: Apply sigma_fin_fun_ext to prove the equality
      apply sigma_fin_fun_ext (decomp_right.1 + 1) (k' + 2) h_fst
      
      -- Step 4: Prove elementwise equality
      intro i
      simp only
      -- Case split on whether i = 0
      by_cases hi : i.val = 0
      · -- Case i = 0: Show ⟨minF, ⟨left, left_ff⟩⟩ = ts 0
        simp only [hi, ↓reduceDIte]
        -- Since i.val = 0, we have i = ⟨0, _⟩
        have hi_eq : i = ⟨0, by omega⟩ := Fin.ext hi
        -- Rewrite ts i to ts ⟨0, _⟩
        conv_rhs => rw [hi_eq]
        -- Now goal is: ⟨minF, ⟨left, left_ff⟩⟩ = ts ⟨0, _⟩
        -- minF = (ts 0).1 by hminF_eq
        -- left = (ts 0).2.val (after casting by hminF_eq)
        -- 
        -- Step 1: Show left.dominos = (ts ⟨0, _⟩).2.val.dominos
        -- left = restrictTilingLeft (n' + 1) T' minF hminF''
        -- T' = hW_eq ▸ (composeTilings (k' + 2) ts).2
        -- T'.dominos = (composeTilings (k' + 2) ts).2.dominos (by Tiling.subst_dominos)
        have hT'_dominos : T'.dominos = (composeTilings (k' + 2) ts).2.dominos := 
          Tiling.subst_dominos hW_eq (composeTilings (k' + 2) ts).2
        have hleft_dominos : left.dominos = (ts ⟨0, by omega⟩).2.val.dominos := by
          simp only [left, restrictTilingLeft]
          -- left.dominos = {d ∈ T'.dominos | d.inLeftPart minF}
          -- We need to show this equals (ts ⟨0, _⟩).2.val.dominos
          -- By hleft_eq, restrictTilingLeft on the original tiling equals (ts ⟨0, _⟩).2.val
          -- So we need to connect T' to the original tiling
          have horiginal : (restrictTilingLeft (composeTilings (k' + 2) ts).1 
              (composeTilings (k' + 2) ts).2 (ts ⟨0, by omega⟩).1 hfault).dominos = 
              (ts ⟨0, by omega⟩).2.val.dominos := by
            rw [hleft_eq]
          simp only [restrictTilingLeft] at horiginal
          -- Now we need: {d ∈ T'.dominos | d.inLeftPart minF} = {d ∈ (composeTilings ...).2.dominos | d.inLeftPart (ts ⟨0, _⟩).1}
          -- Use hT'_dominos and hminF_eq
          have hminF_eq' : minF = (ts ⟨0, by omega⟩).1 := hminF_eq
          rw [hT'_dominos, hminF_eq']
          exact horiginal
        -- Step 2: Destructure ts ⟨0, _⟩ to get concrete values
        -- This allows us to use subst on the width equality
        rcases hts0 : ts ⟨0, by omega⟩ with ⟨w0, T0, hT0_ff⟩
        -- Now hts0 : ts ⟨0, _⟩ = ⟨w0, ⟨T0, hT0_ff⟩⟩
        -- hminF_eq : minF = w0
        simp only [hts0] at hminF_eq
        -- Rewrite hleft_dominos using hts0
        have hleft_dominos' : left.dominos = T0.dominos := by
          rw [hleft_dominos, hts0]
        -- Now minF = w0 and left.dominos = T0.dominos
        -- Use subst to replace minF with w0
        subst hminF_eq
        -- Now minF is replaced by w0, so left : Tiling (Rectangle w0 2)
        -- And T0 : Tiling (Rectangle w0 2) - same type!
        have hleft_val : left = T0 := Tiling.ext left T0 hleft_dominos'
        subst hleft_val
        -- Now left is replaced by T0
        -- Goal: ⟨w0, ⟨T0, left_ff⟩⟩ = ⟨w0, ⟨T0, hT0_ff⟩⟩
        rfl
      · -- Case i > 0: Show decomp_right.2 ⟨i - 1, _⟩ = ts i
        have hi_pos : i.val ≥ 1 := Nat.one_le_iff_ne_zero.mpr hi
        simp only [hi, ↓reduceDIte]
        -- Goal: decomp_right.2 ⟨i.val - 1, _⟩ = ts i
        -- We have hdecomp_tail : decomp_right = ⟨k' + 1, faultfreeTilingsTail (k' + 2) (by omega) ts⟩
        -- 
        -- Extract h1 : decomp_right.1 = k' + 1
        have h1 : decomp_right.1 = k' + 1 := by
          have := congrArg Sigma.fst hdecomp_tail
          simp only at this
          exact this
        -- Use Sigma.ext_iff to extract the HEq of second components
        rw [Sigma.ext_iff] at hdecomp_tail
        obtain ⟨hk, hf⟩ := hdecomp_tail
        -- hk : decomp_right.1 = k' + 1
        -- hf : HEq decomp_right.2 (faultfreeTilingsTail ...)
        -- 
        -- The key is that HEq of functions implies equality of values at HEq indices
        have hindex : HEq (⟨i.val - 1, by omega⟩ : Fin decomp_right.1) 
                          (⟨i.val - 1, by omega⟩ : Fin (k' + 1)) := by
          rw [Fin.heq_ext_iff h1]
        -- Apply congr_heq to get the equality at the specific index
        have happ := congr_heq hf hindex
        -- happ : decomp_right.2 ⟨i.val - 1, _⟩ = faultfreeTilingsTail ... ⟨i.val - 1, _⟩
        rw [happ]
        -- Goal: faultfreeTilingsTail (k' + 2) (by omega) ts ⟨i.val - 1, _⟩ = ts i
        -- By definition: faultfreeTilingsTail k hk ts j = ts ⟨j.val + 1, _⟩
        simp only [faultfreeTilingsTail]
        -- Goal: ts ⟨(i.val - 1) + 1, _⟩ = ts i
        -- Since i.val ≥ 1, we have (i.val - 1) + 1 = i.val
        congr 1
        simp only [Fin.ext_iff]
        omega


/-- The width of the composed tiling equals the sum of widths of the components.
    This follows from the definition of composeTilings as horizontal concatenation. -/
theorem composeTilings_width (k : ℕ) 
    (ts : Fin k → (Σ m : ℕ, {T' : Tiling (Rectangle m 2) // isFaultfree m T'})) :
    (composeTilings k ts).1 = ∑ i : Fin k, (ts i).1 := by
  rfl

/-- The sum of widths of the faultfree tilings equals the width of the original.
    This is the key property that makes the decomposition weight-preserving. -/
theorem decomposeTiling_weight_sum (n : ℕ) (T : Tiling (Rectangle n 2)) :
    let ⟨k, ts⟩ := decomposeTiling n T
    (∑ i : Fin k, (ts i).1) = n := by
  simp only
  have h1 := composeTilings_decomposeTiling n T
  simp only at h1
  have h2 := composeTilings_width (decomposeTiling n T).1 (decomposeTiling n T).2
  rw [← h2]
  exact congrArg Sigma.fst h1

end DominoTilingsZ
end
