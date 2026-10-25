/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift
/-!
# Lifting partition congruences to mex partition functions

This file proves the Barman-Singh lift by removing the forced parts preceding a partition's
minimal excludant and then summing the resulting exact-mex fibers.
-/


namespace MetaMathlibExt

theorem mex_index_not_mem {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) : c (mex_index c hc p) ∉ p.parts := by
  exact Nat.find_spec (mex_exists_missing c hc p)

theorem mex_index_mem_of_lt {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) {i : ℕ} (hi : i < mex_index c hc p) : c i ∈ p.parts := by
  by_contra hmem
  unfold mex_index at hi
  exact (Nat.not_le_of_gt hi) (Nat.find_min' (mex_exists_missing c hc p) hmem)

theorem mex_index_le {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) : mex_index c hc p ≤ N + 1 := by
  apply Nat.find_min' (mex_exists_missing c hc p)
  intro hmem
  have hle := Nat.Partition.le_of_mem_parts hmem
  have hself : N + 1 ≤ c (N + 1) := hc.le_apply
  omega

end MetaMathlibExt
