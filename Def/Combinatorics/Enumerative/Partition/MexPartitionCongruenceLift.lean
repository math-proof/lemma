/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift
/-!
# Lifting partition congruences to mex partition functions

This file proves the Barman-Singh lift by removing the forced parts preceding a partition's
minimal excludant and then summing the resulting exact-mex fibers.
-/


namespace MetaMathlibExt

noncomputable def mex_index {N : ℕ} (c : ℕ → ℕ) (hc : StrictMono c)
    (p : Nat.Partition N) : ℕ :=
  Nat.find (mex_exists_missing c hc p)

end MetaMathlibExt
