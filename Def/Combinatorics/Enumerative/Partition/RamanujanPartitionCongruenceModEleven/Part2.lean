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
import Instance.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruenceModEleven.Part2
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

noncomputable def ramanujanElevenR3 : PowerSeries (ZMod 11) :=
  ramanujanElevenJ 0 ^ 3 * ramanujanElevenJ 3 +
    ramanujanElevenJ 0 * ramanujanElevenJ 1 ^ 3 +
    6 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 * ramanujanElevenJ 3 *
      ramanujanElevenJ 10) +
    7 * (ramanujanElevenJ 1 ^ 2 * ramanujanElevenJ 6 ^ 2) +
    3 * (ramanujanElevenJ 3 * ramanujanElevenJ 6 ^ 2 * ramanujanElevenJ 10) +
    ramanujanElevenJ 6 * ramanujanElevenJ 10 ^ 3

noncomputable def ramanujanElevenR6 : PowerSeries (ZMod 11) :=
  ramanujanElevenJ 0 ^ 3 * ramanujanElevenJ 6 +
    7 * (ramanujanElevenJ 0 ^ 2 * ramanujanElevenJ 3 ^ 2) +
    6 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 * ramanujanElevenJ 6 *
      ramanujanElevenJ 10) +
    ramanujanElevenJ 1 ^ 3 * ramanujanElevenJ 3 +
    3 * (ramanujanElevenJ 1 * ramanujanElevenJ 3 ^ 2 * ramanujanElevenJ 10) +
    ramanujanElevenJ 6 ^ 3 * ramanujanElevenJ 10

noncomputable def ramanujanElevenR8 : PowerSeries (ZMod 11) :=
  3 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 ^ 2 * ramanujanElevenJ 6) +
    6 * (ramanujanElevenJ 0 * ramanujanElevenJ 3 * ramanujanElevenJ 6 *
      ramanujanElevenJ 10) +
    ramanujanElevenJ 0 * ramanujanElevenJ 10 ^ 3 +
    7 * (ramanujanElevenJ 1 ^ 2 * ramanujanElevenJ 3 ^ 2) +
    ramanujanElevenJ 1 * ramanujanElevenJ 6 ^ 3 +
    ramanujanElevenJ 3 ^ 3 * ramanujanElevenJ 10

noncomputable def ramanujanElevenR9 : PowerSeries (ZMod 11) :=
  3 * (ramanujanElevenJ 0 ^ 2 * ramanujanElevenJ 3 * ramanujanElevenJ 6) +
    7 * (ramanujanElevenJ 0 ^ 2 * ramanujanElevenJ 10 ^ 2) +
    ramanujanElevenJ 0 * ramanujanElevenJ 3 ^ 3 +
    6 * (ramanujanElevenJ 1 * ramanujanElevenJ 3 * ramanujanElevenJ 6 *
      ramanujanElevenJ 10) +
    ramanujanElevenJ 1 ^ 3 * ramanujanElevenJ 6 +
    ramanujanElevenJ 1 * ramanujanElevenJ 10 ^ 3

noncomputable def ramanujanElevenR10 : PowerSeries (ZMod 11) :=
  ramanujanElevenJ 0 ^ 3 * ramanujanElevenJ 10 +
    6 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 * ramanujanElevenJ 3 *
      ramanujanElevenJ 6) +
    3 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 * ramanujanElevenJ 10 ^ 2) +
    ramanujanElevenJ 1 * ramanujanElevenJ 3 ^ 3 +
    ramanujanElevenJ 3 * ramanujanElevenJ 6 ^ 3 +
    7 * (ramanujanElevenJ 6 ^ 2 * ramanujanElevenJ 10 ^ 2)

end MetaMathlibExt
