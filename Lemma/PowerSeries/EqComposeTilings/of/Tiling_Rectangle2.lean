import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[compose_tilings_decompose_tiling_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2)) :
-- imply
  let ⟨k, ts⟩ := decomposeTiling n T
  composeTilings k ts = ⟨n, T⟩ := by
-- proof
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


-- created on 2026-10-20
