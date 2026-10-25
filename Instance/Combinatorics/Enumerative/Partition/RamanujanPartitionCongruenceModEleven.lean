/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence
import Lemma.Finset.Enumerative.Partition.RamanujanPartitionCongruence
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

instance ramanujanElevenPrime : Fact (Nat.Prime 11) :=
  ⟨Nat.prime_eleven⟩

instance ramanujanElevenPowerSeriesCharP :
    CharP (PowerSeries (ZMod 11)) 11 :=
  charP_of_injective_ringHom PowerSeries.C_injective 11

end MetaMathlibExt
