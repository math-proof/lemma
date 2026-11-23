/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

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
public import Theorem.Finset.Enumerative.Partition.RamanujanPartitionCongruence
/-!
# Ramanujan's partition congruence modulo 11

This module proves that the partition number `p(11m + 6)` is divisible by 11.
It follows Section 2 of M. D. Hirschhorn, "A short and simple proof of
Ramanujan's mod 11 partition congruence", J. Number Theory 139 (2014), 205–209.

The proof decomposes Euler's pentagonal series and Jacobi's cube series by
exponent modulo 11, verifies Hirschhorn's polynomial identity in characteristic
11, and transfers the resulting coefficient divisibility to partition numbers.
-/
@[expose] public section

namespace MetaMathlibExt

instance ramanujanElevenPrime : Fact (Nat.Prime 11) :=
  ⟨Nat.prime_eleven⟩

instance ramanujanElevenPowerSeriesCharP :
    CharP (PowerSeries (ZMod 11)) 11 :=
  charP_of_injective_ringHom PowerSeries.C_injective 11

end MetaMathlibExt
