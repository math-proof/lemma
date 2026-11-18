module

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence
public import Theorem.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruenceModEleven
public section
/-!
# Ramanujan's partition congruence modulo 11

This module proves that the partition number `p(11m + 6)` is divisible by 11.
It follows Section 2 of M. D. Hirschhorn, "A short and simple proof of
Ramanujan's mod 11 partition congruence", J. Number Theory 139 (2014), 205–209.

The proof decomposes Euler's pentagonal series and Jacobi's cube series by
exponent modulo 11, verifies Hirschhorn's polynomial identity in characteristic
11, and transfers the resulting coefficient divisibility to partition numbers.
-/

namespace MetaMathlibExt

class RamanujanElevenHomogeneous (r : outParam ℕ)
    (f : PowerSeries (ZMod 11)) : Prop where
  supported : ramanujanElevenSupported r f

end MetaMathlibExt
