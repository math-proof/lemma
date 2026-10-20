import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[compose_tilings_no_fault_before_boundary_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k p : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 1)
  (hp : p < (ts ⟨0, hk⟩).1) :
-- imply
  ¬hasFault (composeTilings k ts).1 (composeTilings k ts).2 p := by
-- proof
  intro hfault
  -- If there's a fault at p < (ts 0).1, then the first component would have a fault at p
  -- But the first component is faultfree, contradiction
  have hff := (ts ⟨0, hk⟩).2.property
  have hno_fault := hff.2 p
  apply hno_fault
  -- Show hasFault (ts 0).1 (ts 0).2.val p
  have hpos : p > 0 := hfault.1
  have hlt : p < (ts ⟨0, hk⟩).1 := hp
  constructor
  · exact hpos
  constructor
  · exact hlt
  · -- Show no horizontal domino in (ts 0).2.val crosses position p
    intro d hd
    -- d is in (ts 0).2.val.dominos
    -- The shifted version d.shiftNat 0 = d is in composeTilings_dominos
    have hd_shifted : d.shiftNat (partialWidthSum k ts ⟨0, hk⟩) ∈ (composeTilings k ts).2.dominos := by
      simp only [composeTilings, composeTilings_dominos, Set.mem_iUnion]
      refine ⟨⟨0, hk⟩, ?_⟩
      simp only [composeTilings_component_dominos, Set.mem_image]
      exact ⟨d, hd, rfl⟩
    have hpws0 : partialWidthSum k ts ⟨0, hk⟩ = 0 := partialWidthSum_zero k ts ⟨0, hk⟩ rfl
    simp only [hpws0, Domino.shiftNat_zero] at hd_shifted
    -- Use the fault condition at p in the composed tiling
    have hcross := hfault.2.2 d hd_shifted
    exact hcross


-- created on 2026-10-20
