/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift.Part2
/-!
# Lifting partition congruences to mex partition functions

This file proves the Barman-Singh lift by removing the forced parts preceding a partition's
minimal excludant and then summing the resulting exact-mex fibers.
-/


namespace MetaMathlibExt

def mex_prefix (c : ℕ → ℕ) (j : ℕ) : Multiset ℕ :=
  (Finset.image c (Finset.range j)).val

end MetaMathlibExt
