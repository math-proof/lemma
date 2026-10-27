import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


private lemma sigma_fin_fun_ext {α : Type*} (n m : ℕ) (h : n = m) 
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


/--
[decompose_tiling_compose_tilings_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  decomposeTiling (composeTilings k ts).1 (composeTilings k ts).2 = ⟨k, ts⟩ := by
-- proof
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


-- created on 2026-10-20
