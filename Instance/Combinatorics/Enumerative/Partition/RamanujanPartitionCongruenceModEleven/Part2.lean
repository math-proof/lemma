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
import Class.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruenceModEleven
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

instance ramanujanElevenHomogeneousJ (r : ℕ) :
    RamanujanElevenHomogeneous r (ramanujanElevenJ r) :=
  ⟨ramanujanElevenJ_supported r⟩

instance ramanujanElevenHomogeneousMul {r s : ℕ}
    {f g : PowerSeries (ZMod 11)} [hf : RamanujanElevenHomogeneous r f]
    [hg : RamanujanElevenHomogeneous s g] :
    RamanujanElevenHomogeneous (r + s) (f * g) :=
  ⟨ramanujanElevenSupported_mul hf.supported hg.supported⟩

instance ramanujanElevenHomogeneousPow {r : ℕ}
    {f : PowerSeries (ZMod 11)} [hf : RamanujanElevenHomogeneous r f] (k : ℕ) :
    RamanujanElevenHomogeneous (k * r) (f ^ k) :=
  ⟨ramanujanElevenSupported_pow hf.supported k⟩

instance ramanujanElevenHomogeneousC (a : ZMod 11) :
    RamanujanElevenHomogeneous 0 (PowerSeries.C a) :=
  ⟨ramanujanElevenSupported_C a⟩

instance ramanujanElevenHomogeneousNatCast (n : ℕ) :
    RamanujanElevenHomogeneous 0 (n : PowerSeries (ZMod 11)) := by
  constructor
  simpa only [map_natCast] using ramanujanElevenSupported_C (n : ZMod 11)

instance ramanujanElevenHomogeneousTwo :
    RamanujanElevenHomogeneous 0 (2 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 2

instance ramanujanElevenHomogeneousThree :
    RamanujanElevenHomogeneous 0 (3 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 3

instance ramanujanElevenHomogeneousFour :
    RamanujanElevenHomogeneous 0 (4 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 4

instance ramanujanElevenHomogeneousFive :
    RamanujanElevenHomogeneous 0 (5 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 5

instance ramanujanElevenHomogeneousSix :
    RamanujanElevenHomogeneous 0 (6 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 6

instance ramanujanElevenHomogeneousSeven :
    RamanujanElevenHomogeneous 0 (7 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 7

instance ramanujanElevenHomogeneousEight :
    RamanujanElevenHomogeneous 0 (8 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 8

instance ramanujanElevenHomogeneousNine :
    RamanujanElevenHomogeneous 0 (9 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 9

instance ramanujanElevenHomogeneousTen :
    RamanujanElevenHomogeneous 0 (10 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 10

instance ramanujanElevenHomogeneousTwelve :
    RamanujanElevenHomogeneous 0 (12 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 12

instance ramanujanElevenHomogeneousTwentyFour :
    RamanujanElevenHomogeneous 0 (24 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 24

instance ramanujanElevenHomogeneousTwentyOne :
    RamanujanElevenHomogeneous 0 (21 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 21

instance ramanujanElevenHomogeneousThirtyFive :
    RamanujanElevenHomogeneous 0 (35 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 35

instance ramanujanElevenHomogeneousFortyTwo :
    RamanujanElevenHomogeneous 0 (42 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 42

instance ramanujanElevenHomogeneousOneHundredFive :
    RamanujanElevenHomogeneous 0 (105 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 105

instance ramanujanElevenHomogeneousOneHundredForty :
    RamanujanElevenHomogeneous 0 (140 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 140

instance ramanujanElevenHomogeneousTwoHundredTen :
    RamanujanElevenHomogeneous 0 (210 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 210

instance ramanujanElevenHomogeneousFourHundredTwenty :
    RamanujanElevenHomogeneous 0 (420 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 420

instance ramanujanElevenHomogeneousSixHundredThirty :
    RamanujanElevenHomogeneous 0 (630 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 630

instance ramanujanElevenHomogeneousEightHundredForty :
    RamanujanElevenHomogeneous 0 (840 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 840

instance ramanujanElevenHomogeneousOneThousandTwoHundredSixty :
    RamanujanElevenHomogeneous 0 (1260 : PowerSeries (ZMod 11)) :=
  ramanujanElevenHomogeneousNatCast 1260

end MetaMathlibExt
