import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


private lemma domino_subset_rect (n : ℕ) (T : Tiling (Rectangle n 2)) (d : Domino) (hd : d ∈ T.dominos) :
    d.toShape ⊆ Rectangle n 2 := by
  intro x hx
  have : x ∈ ⋃ d ∈ T.dominos, d.toShape := by
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hx⟩
  rw [T.cover] at this
  exact this


/--
[num_tilings_recurrence_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ) :
-- imply
  numTilings (n + 2) 2 = numTilings n 2 + numTilings (n + 1) 2 := by
-- proof
  -- The proof constructs a bijection between tilings of Rectangle (n+2) 2 and
  -- the disjoint union of tilings of Rectangle n 2 and Rectangle (n+1) 2.
  -- 
  -- The key insight is that every tiling of Rectangle (n+2) 2 has its first column covered 
  -- by either:
  -- 1. A vertical domino at (1,1)-(1,2) (giving a tiling of Rectangle (n+1) 2 after removal and shift)
  -- 2. Two horizontal dominos at (1,1)-(2,1) and (1,2)-(2,2) (giving a tiling of Rectangle n 2 after removal and shift)
  --
  -- The bijection is established using:
  -- - exists_domino_covering_11: there exists a domino covering (1,1)
  -- - domino_covering_11_valid: that domino is either vertical 1 1 or horizontal 1 1
  -- - horizontal_12_if_horizontal_11: if horizontal 1 1 is present, so is horizontal 1 2
  -- - fault_at_1_if_vertical: if vertical 1 1 is present, there's a fault at 1
  -- - fault_at_2_if_horizontal: if horizontal 1 1 is present, there's a fault at 2
  -- - restrictTilingRight: get the right part at a fault
  --
  -- The formal construction uses Equiv.sumCompl to partition tilings by whether 
  -- vertical 1 1 is present, then constructs equivalences for each part.
  unfold numTilings
  -- We need: Nat.card (Tiling (Rectangle (n+2) 2)) = Nat.card (Tiling (Rectangle n 2)) + Nat.card (Tiling (Rectangle (n+1) 2))
  -- 
  -- Define the predicate: P(T) := Domino.vertical 1 1 ∈ T.dominos
  -- Then by Equiv.sumCompl: Tiling (Rectangle (n+2) 2) ≃ {T | P T} ⊕ {T | ¬P T}
  --
  -- We need two equivalences:
  -- e1 : {T | P T} ≃ Tiling (Rectangle (n+1) 2)  (remove vertical, shift by -1)
  -- e2 : {T | ¬P T} ≃ Tiling (Rectangle n 2)     (remove horizontal pair, shift by -2)
  --
  -- The construction of these equivalences requires:
  -- - Forward: use restrictTilingRight with the appropriate fault
  -- - Backward: prepend the appropriate dominos and shift
  --
  -- The equivalence is constructed using the classification of tilings by what covers (1,1).
  -- Every tiling of Rectangle (n+2) 2 has exactly one of:
  -- - vertical 1 1 ∈ T.dominos (covering column 1 with one vertical domino)
  -- - horizontal 1 1 ∈ T.dominos (covering columns 1-2 with two horizontal dominos)
  -- They can't both be present since they overlap at (1,1).
  --
  -- Forward map: T ↦ if vertical 1 1 ∈ T.dominos then Sum.inr (restrictTilingRight T 1)
  --                                               else Sum.inl (restrictTilingRight T 2)
  -- 
  -- Inverse map: Sum.inl T' ↦ prepend {horizontal 1 1, horizontal 1 2} and shift T' by 2
  --              Sum.inr T' ↦ prepend {vertical 1 1} and shift T' by 1
  --
  -- The proof that these are inverses follows from:
  -- 1. At a fault, T.dominos = leftPart ∪ (rightPart.image shiftNat k)
  -- 2. For fault at 1: leftPart = {vertical 1 1}
  -- 3. For fault at 2: leftPart = {horizontal 1 1, horizontal 1 2}
  -- 4. shiftNat and shiftNeg are inverses
  --
  -- This is a standard combinatorial bijection (the Fibonacci recurrence for domino tilings).
  have e : Tiling (Rectangle (n + 2) 2) ≃ Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n + 1) 2) := by
    -- Helper: vertical 1 1 and horizontal 1 1 overlap at (1,1), so they can't both be in a tiling
    have vertical_horizontal_disjoint : ∀ T : Tiling (Rectangle (n + 2) 2), 
        ¬(Domino.vertical 1 1 ∈ T.dominos ∧ Domino.horizontal 1 1 ∈ T.dominos) := by
      intro T ⟨hv, hh⟩
      have hne : Domino.vertical 1 1 ≠ Domino.horizontal 1 1 := by intro h; exact Domino.noConfusion h
      have hdisj := T.pairwise_disjoint hv hh hne
      simp only [Function.onFun] at hdisj
      rw [Set.disjoint_iff_inter_eq_empty] at hdisj
      have h11 : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape ∩ (Domino.horizontal 1 1).toShape := by
        constructor
        · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
        · simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
          left; trivial
      rw [hdisj] at h11
      exact h11
    -- Helper: every tiling of Rectangle (n+2) 2 has either vertical 1 1 or horizontal 1 1
    have classification : ∀ T : Tiling (Rectangle (n + 2) 2), 
        Domino.vertical 1 1 ∈ T.dominos ∨ Domino.horizontal 1 1 ∈ T.dominos := by
      intro T
      obtain ⟨d, hd, hmem⟩ := exists_domino_covering_11 (n + 2) (by omega) T
      have hcases := domino_covering_11_valid (n + 2) T d hd hmem
      rcases hcases with rfl | rfl
      · left; exact hd
      · right; exact hd
    -- Helper: if vertical 1 1 ∈ T.dominos, then horizontal 1 1 ∉ T.dominos
    have vertical_implies_not_horizontal : ∀ T : Tiling (Rectangle (n + 2) 2),
        Domino.vertical 1 1 ∈ T.dominos → Domino.horizontal 1 1 ∉ T.dominos := by
      intro T hv hh
      exact vertical_horizontal_disjoint T ⟨hv, hh⟩
    -- Helper: if vertical 1 1 ∉ T.dominos, then horizontal 1 1 ∈ T.dominos  
    have not_vertical_implies_horizontal : ∀ T : Tiling (Rectangle (n + 2) 2),
        Domino.vertical 1 1 ∉ T.dominos → Domino.horizontal 1 1 ∈ T.dominos := by
      intro T hnv
      rcases classification T with hv | hh
      · exact absurd hv hnv
      · exact hh
    -- Use classical logic for decidability
    have : ∀ T : Tiling (Rectangle (n + 2) 2), Decidable (Domino.vertical 1 1 ∈ T.dominos) := 
      fun T => Classical.dec _
    have : DecidableEq ℕ := Classical.decEq ℕ
    -- Define the forward map
    let toSum : Tiling (Rectangle (n + 2) 2) → Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n + 1) 2) := 
      fun T => if hv : Domino.vertical 1 1 ∈ T.dominos 
               then Sum.inr (restrictTilingRight (n + 2) T 1 (fault_at_1_if_vertical (n + 2) (by omega) T hv))
               else if hn : n = 0 
                    then Sum.inl (hn ▸ emptyTiling2)
                    else Sum.inl (by
                      have hh := not_vertical_implies_horizontal T hv
                      have hn3 : n + 2 ≥ 3 := by omega
                      have hfault := fault_at_2_if_horizontal (n + 2) hn3 T hh
                      have hrestrict := restrictTilingRight (n + 2) T 2 hfault
                      simp only [show n + 2 - 2 = n by omega] at hrestrict
                      exact hrestrict)
    -- Define the inverse map  
    let fromSum : Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n + 1) 2) → Tiling (Rectangle (n + 2) 2) :=
      fun s => match s with
               | Sum.inl T => prependHorizontalPair n T
               | Sum.inr T => prependVertical (n + 1) T
    -- Construct the equivalence
    refine ⟨toSum, fromSum, ?_, ?_⟩
    -- Proof that fromSum ∘ toSum = id (left inverse)
    · intro T
      simp only [toSum, fromSum]
      by_cases hv : Domino.vertical 1 1 ∈ T.dominos
      · -- Case: vertical 1 1 ∈ T.dominos
        simp only [hv, dite_true]
        -- Need to show: prependVertical (n+1) (restrictTilingRight (n+2) T 1 _) = T
        -- This requires showing the dominos are equal
        apply Tiling.ext
        -- Show: {vertical 1 1} ∪ (restrictTilingRight ...).dominos.image (shiftNat 1) = T.dominos
        simp only [prependVertical, restrictTilingRight]
        -- The key insight: T.dominos = {vertical 1 1} ∪ {d ∈ T.dominos | d.inRightPart 1}
        -- because at fault 1, the only domino in left part is vertical 1 1
        ext d
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image, Set.mem_sep_iff]
        constructor
        · intro h
          rcases h with rfl | ⟨d'', ⟨d', ⟨hd'_mem, hd'_right⟩, hd'_eq⟩, hd''_eq⟩
          · exact hv
          · -- d = d''.shiftNat 1 and d'' = d'.shiftNeg 1 and d' ∈ T.dominos
            subst hd'_eq hd''_eq
            rw [Domino.shiftNat_shiftNeg]
            exact hd'_mem
        · intro hd
          have hfault := fault_at_1_if_vertical (n + 2) (by omega) T hv
          have hlr := domino_left_or_right_at_fault hfault d hd
          rcases hlr with hleft | hright
          · -- d is in left part, so d = vertical 1 1
            left
            cases d with
            | horizontal i j =>
              exfalso
              have hsub := domino_subset_rect (n + 2) T (Domino.horizontal i j) hd
              have hi_ge : i ≥ 1 := by
                have := hsub (Set.mem_insert (i, j) _)
                simp only [Rectangle, Set.mem_ofPred_eq] at this
                exact this.1
              have hi1_le : i + 1 ≤ 1 := hleft (i + 1, j) (by simp [Domino.toShape])
              omega
            | vertical i j =>
              have hsub := domino_subset_rect (n + 2) T (Domino.vertical i j) hd
              have h1 : (i, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
              have h2 : (i, j + 1) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
              have hi_ge : i ≥ 1 := by simp only [Rectangle, Set.mem_ofPred_eq] at h1; exact h1.1
              have hi_le : i ≤ 1 := hleft (i, j) (by simp [Domino.toShape])
              have hj_ge : j ≥ 1 := by simp only [Rectangle, Set.mem_ofPred_eq] at h1; exact h1.2.2.1
              have hj1_le : j + 1 ≤ 2 := by simp only [Rectangle, Set.mem_ofPred_eq] at h2; exact h2.2.2.2
              simp only [Domino.vertical.injEq]; omega
          · -- d is in right part
            right
            refine ⟨d.shiftNeg 1, ⟨d, ⟨hd, hright⟩, rfl⟩, Domino.shiftNat_shiftNeg d 1⟩
      · -- Case: vertical 1 1 ∉ T.dominos (so horizontal 1 1 ∈ T.dominos)
        simp only [hv, dite_false]
        by_cases hn : n = 0
        · -- n = 0: special case
          simp only [hn, dite_true]
          -- Need to show: prependHorizontalPair 0 emptyTiling2 = T
          -- When n = 0, Rectangle 2 2 is covered by exactly {horizontal 1 1, horizontal 1 2}
          subst hn
          apply Tiling.ext
          simp only [prependHorizontalPair]
          -- emptyTiling2.dominos = ∅
          have hempty_dominos : emptyTiling2.dominos = ∅ := by
            have hsub : emptyTiling2.dominos ⊆ ∅ := by
              intro d hd
              have hsub' : d.toShape ⊆ Rectangle 0 2 := by
                rw [← emptyTiling2.cover]
                exact Set.subset_biUnion_of_mem hd
              rw [Rectangle_zero_left] at hsub'
              cases d with
              | horizontal i j =>
                have := hsub' (Set.mem_insert (i, j) _)
                exact this
              | vertical i j =>
                have := hsub' (Set.mem_insert (i, j) _)
                exact this
            exact Set.subset_eq_empty hsub rfl
          rw [hempty_dominos, Set.image_empty, Set.union_empty]
          -- Need to show: {horizontal 1 1, horizontal 1 2} = T.dominos
          have hh := not_vertical_implies_horizontal T hv
          have hh2 := horizontal_12_if_horizontal_11 2 (by omega) T hh
          ext d
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · intro hd
            rcases hd with rfl | rfl
            · exact hh
            · exact hh2
          · intro hd
            -- Every domino in T is either horizontal 1 1 or horizontal 1 2
            cases d with
            | horizontal i j =>
              have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
              have h1 : (i, j) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              have h2 : (i + 1, j) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
              have hi : i = 1 := by omega
              have hj : j = 1 ∨ j = 2 := by omega
              rcases hj with rfl | rfl
              · left; simp only [hi]
              · right; simp only [hi]
            | vertical i j =>
              -- vertical dominos are impossible when horizontal 1 1 is present
              exfalso
              have hsub := domino_subset_rect 2 T (Domino.vertical i j) hd
              have h1 : (i, j) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              have h2 : (i, j + 1) ∈ Rectangle 2 2 := hsub (by simp [Domino.toShape])
              simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
              have hi : i = 1 ∨ i = 2 := by omega
              have hj : j = 1 := by omega
              -- If i = 1, then vertical 1 1 ∈ T.dominos, contradicting hv
              -- If i = 2, then vertical 2 1 overlaps with horizontal 1 1 or horizontal 1 2
              rcases hi with rfl | rfl
              · -- i = 1: vertical 1 1 ∈ T.dominos
                have : Domino.vertical 1 1 ∈ T.dominos := by simp only [hj] at hd; exact hd
                exact hv this
              · -- i = 2: vertical 2 1 overlaps with horizontal 1 1 at (2, 1)
                have hdisj := T.pairwise_disjoint hh hd
                have hne : Domino.horizontal 1 1 ≠ Domino.vertical 2 j := by simp
                have : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 2 j).toShape := hdisj hne
                have h21_h : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
                have h21_v : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 2 j).toShape := by simp [Domino.toShape, hj]
                exact Set.disjoint_iff.mp this ⟨h21_h, h21_v⟩
        · -- n ≥ 1: use restrictTilingRight
          simp only [hn, dite_false]
          -- Need to show: prependHorizontalPair n (restrictTilingRight (n+2) T 2 _) = T
          apply Tiling.ext
          simp only [prependHorizontalPair, restrictTilingRight]
          -- Similar to the vertical case: T.dominos = {h 1 1, h 1 2} ∪ {d ∈ T.dominos | d.inRightPart 2}
          ext d
          simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
          constructor
          · intro h
            rcases h with (rfl | rfl) | ⟨d'', ⟨d', ⟨hd'_mem, hd'_right⟩, hd'_eq⟩, hd''_eq⟩
            · exact not_vertical_implies_horizontal T hv
            · exact horizontal_12_if_horizontal_11 (n + 2) (by omega) T (not_vertical_implies_horizontal T hv)
            · subst hd'_eq hd''_eq; rw [Domino.shiftNat_shiftNeg]; exact hd'_mem
          · intro hd
            have hh := not_vertical_implies_horizontal T hv
            have hn3 : n + 2 ≥ 3 := by omega
            have hfault := fault_at_2_if_horizontal (n + 2) hn3 T hh
            have hlr := domino_left_or_right_at_fault hfault d hd
            rcases hlr with hleft | hright
            · -- d is in left part at fault 2, so d = horizontal 1 1 or horizontal 1 2
              cases d with
              | horizontal i j =>
                have hsub := domino_subset_rect (n + 2) T (Domino.horizontal i j) hd
                have h1 : (i, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                have h2 : (i + 1, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
                have hi1_le : i + 1 ≤ 2 := hleft (i + 1, j) (by simp [Domino.toShape])
                have hi_ge : i ≥ 1 := h1.1
                have hj12 : j = 1 ∨ j = 2 := by omega
                have hi_eq : i = 1 := by omega
                rcases hj12 with rfl | rfl
                · left; left; simp only [hi_eq]
                · left; right; simp only [hi_eq]
              | vertical i j =>
                exfalso
                have hsub := domino_subset_rect (n + 2) T (Domino.vertical i j) hd
                have h1 : (i, j) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1
                have hi_ge : i ≥ 1 := h1.1
                have hi_le : i ≤ 2 := hleft (i, j) (by simp [Domino.toShape])
                have hj_ge : j ≥ 1 := h1.2.2.1
                -- vertical i j with 1 ≤ i ≤ 2 and j ≥ 1 means i ∈ {1, 2}
                -- If i = 1: vertical 1 1 ∈ T.dominos, contradicting hv
                -- If i = 2: vertical 2 j overlaps with horizontal 1 j at (2, j)
                rcases (show i = 1 ∨ i = 2 by omega) with hi_eq | hi_eq
                · have hj1 : j = 1 := by
                    have h2' : (i, j + 1) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                    simp only [Rectangle, Set.mem_ofPred_eq] at h2'
                    omega
                  have hv11 : Domino.vertical 1 1 ∈ T.dominos := by
                    simp only [hi_eq, hj1] at hd; exact hd
                  exact hv hv11
                · have hj12 : j = 1 := by
                    have h2' : (i, j + 1) ∈ Rectangle (n + 2) 2 := hsub (by simp [Domino.toShape])
                    simp only [Rectangle, Set.mem_ofPred_eq] at h2'
                    omega
                  have hh2 := horizontal_12_if_horizontal_11 (n + 2) (by omega) T hh
                  have hdisj := T.pairwise_disjoint hh hd
                  have hne : Domino.horizontal 1 1 ≠ Domino.vertical i j := by simp [hi_eq]
                  have hdisj' : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical i j).toShape := hdisj hne
                  have h21_h : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
                  have h21_v : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.vertical i j).toShape := by simp [Domino.toShape, hi_eq, hj12]
                  exact Set.disjoint_iff.mp hdisj' ⟨h21_h, h21_v⟩
            · -- d is in right part
              right
              refine ⟨d.shiftNeg 2, ⟨d, ⟨hd, hright⟩, rfl⟩, Domino.shiftNat_shiftNeg d 2⟩
    -- Proof that toSum ∘ fromSum = id (right inverse)
    · intro s
      simp only [toSum, fromSum]
      rcases s with T | T
      · -- Case: Sum.inl T (from Rectangle n 2)
        -- Need to show: toSum (prependHorizontalPair n T) = Sum.inl T
        -- First, show vertical 1 1 ∉ (prependHorizontalPair n T).dominos
        have hv_not : Domino.vertical 1 1 ∉ (prependHorizontalPair n T).dominos := by
          simp only [prependHorizontalPair, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          constructor
          · constructor
            · exact fun h => Domino.noConfusion h
            · exact fun h => Domino.noConfusion h
          · exact vertical_11_not_in_shiftNat2_image n T
        simp only [hv_not, dite_false]
        by_cases hn : n = 0
        · simp only [hn, dite_true]
          -- Need to show: Sum.inl (0 ▸ emptyTiling2) = Sum.inl T
          -- When n = 0, T : Tiling (Rectangle 0 2) must be emptyTiling2
          subst hn
          congr 1
          apply Tiling.ext
          -- Rectangle 0 2 = ∅, so both tilings have empty dominos
          have hT_empty : T.dominos = ∅ := by
            have hsub : T.dominos ⊆ ∅ := by
              intro d hd
              have hsub' : d.toShape ⊆ Rectangle 0 2 := by
                rw [← T.cover]
                exact Set.subset_biUnion_of_mem hd
              rw [Rectangle_zero_left] at hsub'
              cases d with
              | horizontal i j => exact hsub' (Set.mem_insert (i, j) _)
              | vertical i j => exact hsub' (Set.mem_insert (i, j) _)
            exact Set.subset_eq_empty hsub rfl
          have hempty : emptyTiling2.dominos = ∅ := by
            have hsub : emptyTiling2.dominos ⊆ ∅ := by
              intro d hd
              have hsub' : d.toShape ⊆ Rectangle 0 2 := by
                rw [← emptyTiling2.cover]
                exact Set.subset_biUnion_of_mem hd
              rw [Rectangle_zero_left] at hsub'
              cases d with
              | horizontal i j => exact hsub' (Set.mem_insert (i, j) _)
              | vertical i j => exact hsub' (Set.mem_insert (i, j) _)
            exact Set.subset_eq_empty hsub rfl
          rw [hT_empty, hempty]
        · simp only [hn, dite_false]
          -- Need to show: Sum.inl (restrictTilingRight ...) = Sum.inl T
          -- This means restrictTilingRight (prependHorizontalPair n T) = T
          congr 1
          apply Tiling.ext
          simp only [restrictTilingRight, prependHorizontalPair]
          -- Similar to the vertical case
          ext d
          simp only [Set.mem_image, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · intro ⟨d', ⟨hd'_mem, hd'_right⟩, hd_eq⟩
            cases hd'_mem with
            | inl heq =>
              rcases heq with rfl | rfl
              · -- d' = horizontal 1 1, which is in left part at fault 2
                exfalso
                have h : (2 : ℤ) ≥ 2 + 1 := hd'_right (2, 1) (by simp [Domino.toShape])
                omega
              · -- d' = horizontal 1 2, which is in left part at fault 2
                exfalso
                have h : (2 : ℤ) ≥ 2 + 1 := hd'_right (2, 2) (by simp [Domino.toShape])
                omega
            | inr hex =>
              obtain ⟨d'', hd''_mem, hd''_eq⟩ := hex
              subst hd''_eq hd_eq
              simp only [Domino.shiftNeg_shiftNat]
              exact hd''_mem
          · intro hd
            use d.shiftNat 2
            constructor
            · constructor
              · right; exact ⟨d, hd, rfl⟩
              · simp only [Domino.inRightPart, Domino.shiftNat_toShape]
                intro p hp
                simp only [Set.mem_image] at hp
                obtain ⟨⟨x, y⟩, hxy, rfl, rfl⟩ := hp
                have hsub := domino_subset_rect n T d hd
                cases d with
                | horizontal i j =>
                  have h1 : (i, j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
                  simp only [Rectangle, Set.mem_ofPred_eq] at h1
                  simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
                | vertical i j =>
                  have h1 : (i, j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
                  simp only [Rectangle, Set.mem_ofPred_eq] at h1
                  simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
            · exact Domino.shiftNeg_shiftNat d 2
      · -- Case: Sum.inr T (from Rectangle (n+1) 2)
        -- Need to show: toSum (prependVertical (n+1) T) = Sum.inr T
        -- First, show vertical 1 1 ∈ (prependVertical (n+1) T).dominos
        have hv : Domino.vertical 1 1 ∈ (prependVertical (n + 1) T).dominos := by
          simp only [prependVertical, Set.mem_union, Set.mem_singleton_iff, true_or]
        simp only [hv, dite_true]
        -- Need to show: Sum.inr (restrictTilingRight ...) = Sum.inr T
        -- This means restrictTilingRight (prependVertical (n+1) T) = T
        congr 1
        apply Tiling.ext
        simp only [restrictTilingRight, prependVertical]
        -- The right part of prependVertical T at fault 1 is exactly T.dominos.image (shiftNat 1)
        -- And restricting shifts back by 1, so we get T.dominos
        ext d
        simp only [Set.mem_image, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · intro ⟨d', ⟨hd'_mem, hd'_right⟩, hd_eq⟩
          cases hd'_mem with
          | inl heq =>
            -- d' = vertical 1 1, which is in left part, not right part
            exfalso
            subst heq
            have h : (1 : ℤ) ≥ 1 + 1 := hd'_right (1, 1) (by simp [Domino.toShape])
            omega
          | inr hex =>
            -- d' is in the shifted part
            obtain ⟨d'', hd''_mem, hd''_eq⟩ := hex
            subst hd''_eq hd_eq
            simp only [Domino.shiftNeg_shiftNat]
            exact hd''_mem
        · intro hd
          use d.shiftNat 1
          constructor
          · constructor
            · right; exact ⟨d, hd, rfl⟩
            · simp only [Domino.inRightPart, Domino.shiftNat_toShape]
              intro p hp
              simp only [Set.mem_image] at hp
              obtain ⟨⟨x, y⟩, hxy, rfl, rfl⟩ := hp
              have hsub := domino_subset_rect (n + 1) T d hd
              cases d with
              | horizontal i j =>
                have h1 : (i, j) ∈ Rectangle (n + 1) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1
                simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
              | vertical i j =>
                have h1 : (i, j) ∈ Rectangle (n + 1) 2 := hsub (by simp [Domino.toShape])
                simp only [Rectangle, Set.mem_ofPred_eq] at h1
                simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff] at hxy
                rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
          · exact Domino.shiftNeg_shiftNat d 1
  -- Provide Finite instances by extracting from tilingsHeight2_isFiniteType
  -- tilingsHeight2_isFiniteType k says {a : Σ n, Tiling (Rectangle n 2) | weight a = k} is finite
  -- This implies Tiling (Rectangle k 2) is finite
  have hfin_n : Set.Finite (Set.univ : Set (Tiling (Rectangle n 2))) := by
    have h := tilingsHeight2_isFiniteType n
    let f : Tiling (Rectangle n 2) → Σ m : ℕ, Tiling (Rectangle m 2) := fun T => ⟨n, T⟩
    have hf : Function.Injective f := by
      intro T1 T2 heq
      simp only [f, Sigma.mk.injEq] at heq
      exact eq_of_heq heq.2
    have hrange : Set.range f ⊆ {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n} := by
      intro x hx
      simp only [Set.mem_range, f] at hx
      obtain ⟨T, rfl⟩ := hx
      simp only [TilingsHeight2, Set.mem_ofPred_eq]
    have hrange_fin : Set.Finite (Set.range f) := h.subset hrange
    convert hrange_fin.preimage hf.injOn
    ext T
    simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, true_iff]
    exact ⟨T, rfl⟩
  have hfin_n1 : Set.Finite (Set.univ : Set (Tiling (Rectangle (n + 1) 2))) := by
    have h := tilingsHeight2_isFiniteType (n + 1)
    let f : Tiling (Rectangle (n + 1) 2) → Σ m : ℕ, Tiling (Rectangle m 2) := fun T => ⟨n + 1, T⟩
    have hf : Function.Injective f := by
      intro T1 T2 heq
      simp only [f, Sigma.mk.injEq] at heq
      exact eq_of_heq heq.2
    have hrange : Set.range f ⊆ {a : Σ m : ℕ, Tiling (Rectangle m 2) | TilingsHeight2.weight a = n + 1} := by
      intro x hx
      simp only [Set.mem_range, f] at hx
      obtain ⟨T, rfl⟩ := hx
      simp only [TilingsHeight2, Set.mem_ofPred_eq]
    have hrange_fin : Set.Finite (Set.range f) := h.subset hrange
    convert hrange_fin.preimage hf.injOn
    ext T
    simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, true_iff]
    exact ⟨T, rfl⟩
  have : Finite (Tiling (Rectangle n 2)) := Set.finite_univ_iff.mp hfin_n
  have : Finite (Tiling (Rectangle (n + 1) 2)) := Set.finite_univ_iff.mp hfin_n1
  rw [Nat.card_congr e, Nat.card_sum, add_comm]


-- created on 2026-10-20
