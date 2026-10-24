import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[restrict_tiling_right_compose_tilings_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
-- imply
  (restrictTilingRight (composeTilings k ts).1 (composeTilings k ts).2
        (ts ⟨0, by omega⟩).1 hfault).dominos =
      (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).2.dominos := by
-- proof
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


-- created on 2026-10-20
