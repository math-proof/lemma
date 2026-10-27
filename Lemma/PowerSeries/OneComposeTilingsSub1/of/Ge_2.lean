import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[compose_tilings_tail_width_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (hk : k ≥ 2)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  (composeTilings (k - 1) (faultfreeTilingsTail k (by omega) ts)).1 =
      (composeTilings k ts).1 - (ts ⟨0, by omega⟩).1 := by
-- proof
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


-- created on 2026-10-20
