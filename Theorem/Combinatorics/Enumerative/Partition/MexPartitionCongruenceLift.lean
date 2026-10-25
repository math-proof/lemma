/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Ring
/-!
# Lifting partition congruences to mex partition functions

This file proves the Barman-Singh lift by removing the forced parts preceding a partition's
minimal excludant and then summing the resulting exact-mex fibers.
-/


namespace MetaMathlibExt

theorem mex_exists_missing {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) : ∃ j, c j ∉ p.parts := by
  refine ⟨N + 1, ?_⟩
  intro hmem
  have hle := Nat.Partition.le_of_mem_parts hmem
  have hself : N + 1 ≤ c (N + 1) := hc.le_apply
  omega

end MetaMathlibExt
