import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[compose_tilings_one_is_faultfree_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (ts : Fin 1 → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  isFaultfree (composeTilings 1 ts).1 (composeTilings 1 ts).2 := by
-- proof
  have h := (ts 0).2.property
  -- The width is (ts 0).1 and the tiling has the same dominos as (ts 0).2.val
  -- Since (ts 0).2.val is faultfree, so is the composed tiling
  constructor
  · -- Positive width
    have hpos : (ts 0).1 > 0 := h.1
    simp only [composeTilings, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
    exact hpos
  · -- No faults
    intro k hfault
    have hno_fault := h.2 k
    apply hno_fault
    rw [hasFault_eq_of_dominos_eq (composeTilings_one_dominos ts).symm]
    simp only [composeTilings] at hfault ⊢
    exact hfault


-- created on 2026-10-20
