/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift.Part4

@[expose] public section

/-!
# Lifting partition congruences to mex partition functions

This file proves the Barman-Singh lift by removing the forced parts preceding a partition's
minimal excludant and then summing the resulting exact-mex fibers.
-/


namespace MetaMathlibExt

def mex_linear_candidate (A i : ℕ) : ℕ := A * (i + 1)

def mex_odd_candidate (A i : ℕ) : ℕ := A * (2 * i + 1)

end MetaMathlibExt
