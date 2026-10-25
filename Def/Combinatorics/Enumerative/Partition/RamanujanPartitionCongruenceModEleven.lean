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
import Instance.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruenceModEleven
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

/-- Euler's pentagonal series reduced modulo 11. -/
noncomputable def ramanujanElevenEuler : PowerSeries (ZMod 11) :=
  PowerSeries.map (Int.castRingHom (ZMod 11)) (PowerSeries.pentagonalSeries ℤ)

/-- Jacobi's cube series reduced modulo 11. -/
noncomputable def ramanujanElevenJacobi : PowerSeries (ZMod 11) :=
  PowerSeries.map (Int.castRingHom (ZMod 11)) jacobiCubeSeries

/-- The part of a power series whose exponents are congruent to `r` modulo 11. -/
noncomputable def ramanujanElevenSection (r : ℕ) (f : PowerSeries (ZMod 11)) :
    PowerSeries (ZMod 11) :=
  PowerSeries.mk fun n => if n ≡ r [MOD 11] then PowerSeries.coeff n f else 0

/-- The residue-`r` part of Jacobi's cube series modulo 11. -/
noncomputable def ramanujanElevenJ (r : ℕ) : PowerSeries (ZMod 11) :=
  ramanujanElevenSection r ramanujanElevenJacobi

/-- A series is supported in one congruence class modulo 11. -/
def ramanujanElevenSupported (r : ℕ) (f : PowerSeries (ZMod 11)) : Prop :=
  ∀ n : ℕ, ¬n ≡ r [MOD 11] → PowerSeries.coeff n f = 0

end MetaMathlibExt
