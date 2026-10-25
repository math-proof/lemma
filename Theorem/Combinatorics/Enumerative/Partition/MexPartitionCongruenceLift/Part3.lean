/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift.Part2
/-!
# Lifting partition congruences to mex partition functions

This file proves the Barman-Singh lift by removing the forced parts preceding a partition's
minimal excludant and then summing the resulting exact-mex fibers.
-/


namespace MetaMathlibExt

theorem mex_index_eq_iff {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) (j : ℕ) :
    mex_index c hc p = j ↔ mex_prefix c j ≤ p.parts ∧ c j ∉ p.parts := by
  constructor
  · intro h
    subst j
    refine ⟨(mex_prefix_le_iff c _ p).2 ?_, mex_index_not_mem c hc p⟩
    exact fun i hi => mex_index_mem_of_lt c hc p hi
  · rintro ⟨hprefix, hmissing⟩
    have hle : mex_index c hc p ≤ j := by
      unfold mex_index
      exact Nat.find_min' (mex_exists_missing c hc p) hmissing
    have hnot : ¬mex_index c hc p < j := by
      intro hlt
      exact (mex_index_not_mem c hc p) ((mex_prefix_le_iff c j p).1 hprefix _ hlt)
    exact Nat.le_antisymm hle (Nat.not_lt.mp hnot)

end MetaMathlibExt
