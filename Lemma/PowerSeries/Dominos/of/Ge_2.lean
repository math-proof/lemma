import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[restrict_tiling_left_compose_tilings_dominos_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hfault : hasFault (composeTilings k ts).1 (composeTilings k ts).2 (ts ⟨0, by omega⟩).1) :
-- imply
  (restrictTilingLeft (composeTilings k ts).1 (composeTilings k ts).2
    (ts ⟨0, by omega⟩).1 hfault).dominos = (ts ⟨0, by omega⟩).2.val.dominos := by
-- proof
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


-- created on 2026-10-20
