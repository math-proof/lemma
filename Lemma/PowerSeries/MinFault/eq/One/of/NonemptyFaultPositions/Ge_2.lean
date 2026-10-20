import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[compose_tilings_min_fault_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')))
  (hk : k ≥ 2)
  (hne : (faultPositions (composeTilings k ts).1 (composeTilings k ts).2).Nonempty) :
-- imply
  minFault (composeTilings k ts).1 (composeTilings k ts).2 hne = (ts ⟨0, by omega⟩).1 := by
-- proof
  -- The minimum fault is (ts 0).1 because:
  -- 1. There's a fault at (ts 0).1 (by composeTilings_hasFault_at_boundary)
  -- 2. There are no faults at positions < (ts 0).1 (by composeTilings_no_fault_before_boundary)
  have hfault := composeTilings_hasFault_at_boundary k hk ts
  have hmin := minFault_hasFault (composeTilings k ts).1 (composeTilings k ts).2 hne
  have hle := minFault_le (composeTilings k ts).1 (composeTilings k ts).2 hne (ts ⟨0, by omega⟩).1 hfault
  -- Show minFault >= (ts 0).1 by contradiction
  by_contra hne'
  push Not at hne'
  have hlt : minFault (composeTilings k ts).1 (composeTilings k ts).2 hne < (ts ⟨0, by omega⟩).1 := by
    omega
  have hno := composeTilings_no_fault_before_boundary k (by omega : k ≥ 1) ts 
    (minFault (composeTilings k ts).1 (composeTilings k ts).2 hne) hlt
  exact hno hmin


-- created on 2026-10-20
