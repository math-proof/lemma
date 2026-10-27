import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[decompose_tiling_has_fault_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle (n + 1) 2))
  (hne : (faultPositions (n + 1) T).Nonempty) :
-- imply
  let k := minFault (n + 1) T hne
  let hk := minFault_hasFault (n + 1) T hne
  let hk_min : ∀ j, j < k → ¬hasFault (n + 1) T j := fun j hj hfault =>
    absurd (minFault_le (n + 1) T hne j hfault) (not_le.mpr hj)
  let left := restrictTilingLeft (n + 1) T k hk
  let left_ff := restrictTilingLeft_isFaultfree (n + 1) T k hk hk_min
  let right := restrictTilingRight (n + 1) T k hk
  let ⟨m, ts⟩ := decomposeTiling (n + 1 - k) right
  decomposeTiling (n + 1) T =
    ⟨m + 1, fun i => if hi : i.val = 0 then ⟨k, ⟨left, left_ff⟩⟩
                     else ts ⟨i.val - 1, by omega⟩⟩ := by
-- proof
  simp only [decomposeTiling, dite_eq_left hne]


-- created on 2026-10-20
