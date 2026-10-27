import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[partial_width_sum_tail_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (hk : k ≥ 2)
  (j : Fin (k - 1))
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  partialWidthSum (k - 1) (faultfreeTilingsTail k (by omega) ts) j =
    partialWidthSum k ts ⟨j.val + 1, by omega⟩ - (ts ⟨0, by omega⟩).1 := by
-- proof
  simp only [partialWidthSum, faultfreeTilingsTail]
  -- LHS: ∑ i : Fin j.val, (ts ⟨i.val + 1, ...⟩).1
  -- RHS: ∑ i : Fin (j.val + 1), (ts ⟨i.val, ...⟩).1 - (ts ⟨0, ...⟩).1
  -- Use Fin.sum_univ_succ on RHS
  have hrhs : ∑ i : Fin (j.val + 1), (ts ⟨i.val, by omega⟩).1 = 
              (ts ⟨0, by omega⟩).1 + ∑ i : Fin j.val, (ts ⟨i.succ.val, by omega⟩).1 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero]
  conv_rhs => rw [hrhs]
  -- Now goal: ∑ i : Fin j.val, (ts ⟨i.val + 1, ...⟩).1 = 
  --           (ts ⟨0, ...⟩).1 + ∑ i : Fin j.val, (ts ⟨i.succ.val, ...⟩).1 - (ts ⟨0, ...⟩).1
  -- Note: i.succ.val = i.val + 1
  have heq : ∑ i : Fin j.val, (ts ⟨i.succ.val, by omega⟩).1 = 
             ∑ i : Fin j.val, (ts ⟨i.val + 1, by omega⟩).1 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_succ]
  rw [heq]
  omega


-- created on 2026-10-20
