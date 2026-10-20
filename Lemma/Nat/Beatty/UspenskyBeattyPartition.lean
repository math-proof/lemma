import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Beatty.UspenskyBeattyPartition
open MetaMathlibExt


/--
[uspensky_no_partition_into_three_or_more_beatty_sequences](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Beatty/UspenskyBeattyPartition.lean)
-/
@[path]
private lemma uspensky_no_partition_into_three_or_more_beatty_sequences_eq
  {k : ℕ}
  {α : Fin k → ℝ}
-- given
  (hk : 3 ≤ k)
  (hαpos : ∀ i, 0 < α i)
  (hαlt : ∀ i, α i < 1) :
-- imply
  ¬ ((Set.univ : Set (Fin k)).PairwiseDisjoint
    (fun i => {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) ∧
    (⋃ i, {x : ℤ | ∃ n : ℤ, 0 < n ∧ beattySeq (1 / α i) n = x}) =
    {x : ℤ | 0 < x}) := by
-- proof
  apply MetaMathlibExt.uspensky_no_partition_into_three_or_more_beatty_sequences k hk α hαpos hαlt


-- created on 2026-10-20
